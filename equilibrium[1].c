/* Equilibrium - Personal Expense & Budget Tracker (single-file C web server) */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
typedef unsigned int u32;
#define NC 9
#define MAXT 5000
static const char *CATS[NC]={"Food","Rent","Transport","Shopping","Bills","Health","Education","Entertainment","Other"};
static char DIR_[200]="data", ADMIN_U[24]="admin";
static const u32 K[64]={0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static u32 rr(u32 x,int n){return (x>>n)|(x<<(32-n));}
static void sha256(const char *s,char *out){
 u32 h[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
 size_t n=strlen(s),tot=((n+8)/64+1)*64; unsigned char *m=calloc(tot,1);
 memcpy(m,s,n); m[n]=0x80; unsigned long long bits=(unsigned long long)n*8;
 for(int i=0;i<8;i++) m[tot-1-i]=(unsigned char)(bits>>(8*i));
 for(size_t o=0;o<tot;o+=64){
  u32 w[64]; for(int i=0;i<16;i++) w[i]=((u32)m[o+4*i]<<24)|((u32)m[o+4*i+1]<<16)|((u32)m[o+4*i+2]<<8)|m[o+4*i+3];
  for(int i=16;i<64;i++){u32 s0=rr(w[i-15],7)^rr(w[i-15],18)^(w[i-15]>>3),s1=rr(w[i-2],17)^rr(w[i-2],19)^(w[i-2]>>10);w[i]=w[i-16]+s0+w[i-7]+s1;}
  u32 a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
  for(int i=0;i<64;i++){u32 S1=rr(e,6)^rr(e,11)^rr(e,25),ch=(e&f)^(~e&g),t1=hh+S1+ch+K[i]+w[i],S0=rr(a,2)^rr(a,13)^rr(a,22),mj=(a&b)^(a&c)^(b&c),t2=S0+mj;hh=g;g=f;f=e;e=d+t1;d=c;c=b;b=a;a=t1+t2;}
  h[0]+=a;h[1]+=b;h[2]+=c;h[3]+=d;h[4]+=e;h[5]+=f;h[6]+=g;h[7]+=hh;}
 free(m); for(int i=0;i<8;i++) sprintf(out+8*i,"%08x",h[i]);
}
static void phash(const char *u,const char *p,char *out){char b[256];snprintf(b,sizeof b,"equilibrium:%s:%s",u,p);sha256(b,out);}
/* ---------- sessions ---------- */
typedef struct{char tok[33];char user[24];}Sess;
static Sess S[256]; static int ns=0;
static void newtok(char *t){FILE *r=fopen("/dev/urandom","rb");unsigned char b[16]={0};if(r){if(fread(b,1,16,r)!=16)b[0]=(unsigned char)time(NULL);fclose(r);}for(int i=0;i<16;i++)sprintf(t+2*i,"%02x",b[i]);}
static const char *sess_user(const char *tok){if(!tok||!*tok)return NULL;for(int i=0;i<256;i++)if(S[i].tok[0]&&!strcmp(S[i].tok,tok))return S[i].user;return NULL;}
static void sess_kill_user(const char *u){for(int i=0;i<256;i++)if(!strcmp(S[i].user,u))S[i].tok[0]=0;}
/* ---------- helpers ---------- */
static void udec(const char *s,size_t n,char *o,size_t cap){size_t j=0;for(size_t i=0;i<n&&j+1<cap;i++){if(s[i]=='+')o[j++]=' ';else if(s[i]=='%'&&i+2<n){char h[3]={s[i+1],s[i+2],0};unsigned v;if(sscanf(h,"%2x",&v)==1){o[j++]=v?(char)v:' ';i+=2;}else o[j++]='%';}else o[j++]=s[i];}o[j]=0;}
static int field(const char *b,const char *k,char *o,size_t cap){size_t kl=strlen(k);const char *p=b;o[0]=0;while(*p){const char *e=strchr(p,'&');size_t len=e?(size_t)(e-p):strlen(p);if(len>kl&&!strncmp(p,k,kl)&&p[kl]=='='){udec(p+kl+1,len-kl-1,o,cap);return 1;}if(!e)break;p=e+1;}return 0;}
static void esc(FILE *f,const char *s){for(;*s;s++){switch(*s){case '<':fputs("&lt;",f);break;case '>':fputs("&gt;",f);break;case '&':fputs("&amp;",f);break;case '"':fputs("&quot;",f);break;case '\'':fputs("&#39;",f);break;default:fputc(*s,f);}}}
static int valid_user(const char *s){size_t n=strlen(s);if(n<3||n>20)return 0;for(;*s;s++)if(!isalnum((unsigned char)*s)&&*s!='_')return 0;return 1;}
static void clean(char *s){for(;*s;s++)if((unsigned char)*s<32||*s=='|')*s=' ';}
static void upath(char *o,size_t n,const char *pre,const char *u){snprintf(o,n,"%s/%s_%s.db",DIR_,pre,u);}
static int find_user(const char *name,char *hash,char *role){char p[300];snprintf(p,sizeof p,"%s/users.db",DIR_);FILE *f=fopen(p,"r");if(!f)return 0;char u[32],h[80],r[16];int ok=0;while(fscanf(f,"%31s %79s %15s",u,h,r)==3)if(!strcmp(u,name)){if(hash)strcpy(hash,h);if(role)strcpy(role,r);ok=1;break;}fclose(f);return ok;}
static void set_user(const char *name,const char *hash,const char *role){char p[300],t[320];snprintf(p,sizeof p,"%s/users.db",DIR_);snprintf(t,sizeof t,"%s.tmp",p);FILE *in=fopen(p,"r"),*out=fopen(t,"w");if(!out){if(in)fclose(in);return;}char u[32],h[80],r[16];if(in){while(fscanf(in,"%31s %79s %15s",u,h,r)==3)if(strcmp(u,name))fprintf(out,"%s %s %s\n",u,h,r);fclose(in);}fprintf(out,"%s %s %s\n",name,hash,role);fclose(out);rename(t,p);}
static void del_user(const char *name){char p[300],t[320];snprintf(p,sizeof p,"%s/users.db",DIR_);snprintf(t,sizeof t,"%s.tmp",p);FILE *in=fopen(p,"r"),*out=fopen(t,"w");if(!in||!out){if(in)fclose(in);if(out)fclose(out);return;}char u[32],h[80],r[16];while(fscanf(in,"%31s %79s %15s",u,h,r)==3)if(strcmp(u,name))fprintf(out,"%s %s %s\n",u,h,r);fclose(in);fclose(out);rename(t,p);upath(p,sizeof p,"tx",name);remove(p);upath(p,sizeof p,"bud",name);remove(p);sess_kill_user(name);}
typedef struct{int id;char type;char cat[16];double amt;char date[11];char note[80];}T;
static T TX[MAXT];
static int load(const char *u){char p[300];upath(p,sizeof p,"tx",u);FILE *f=fopen(p,"r");if(!f)return 0;int n=0;char line[256];while(n<MAXT&&fgets(line,sizeof line,f)){T *t=&TX[n];t->note[0]=0;if(sscanf(line,"%d|%c|%15[^|]|%lf|%10[^|]|%79[^\n]",&t->id,&t->type,t->cat,&t->amt,t->date,t->note)>=5)n++;}fclose(f);return n;}
static void load_bud(const char *u,double *b){for(int i=0;i<NC;i++)b[i]=0;char p[300];upath(p,sizeof p,"bud",u);FILE *f=fopen(p,"r");if(!f)return;char c[16];double a;while(fscanf(f,"%15s %lf",c,&a)==2)for(int i=0;i<NC;i++)if(!strcmp(c,CATS[i]))b[i]=a;fclose(f);}
static int cat_idx(const char *c){for(int i=0;i<NC;i++)if(!strcmp(c,CATS[i]))return i;return -1;}
/* ---------- HTTP out ---------- */
static const char *MSG[]={"","Wrong username or password.","Username must be 3-20 letters, numbers or _ .","Password must be at least 6 characters.","That username is already taken.","Account created. Please log in.","Please enter a valid amount, category and date.","Saved.","Too many records stored.","Not allowed."};
static const char *CSS="<style>*{box-sizing:border-box}body{margin:0;font-family:system-ui,Segoe UI,Arial,sans-serif;background:#f1f6f4;color:#1b2b27}header{background:#0f5c4d;color:#fff;padding:14px 24px;display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px}header h1{margin:0;font-size:22px;letter-spacing:1px}header a,header span{color:#fff;margin-left:14px;font-size:14px}main{max-width:1000px;margin:20px auto;padding:0 14px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:14px}.card{background:#fff;border-radius:10px;padding:16px;box-shadow:0 1px 4px #0001;margin-bottom:14px}.stat{font-size:26px;font-weight:700}.inc{color:#0a8a4a}.exp{color:#c0392b}label{display:block;font-size:13px;margin:8px 0 3px}input,select,button{width:100%;padding:9px;border:1px solid #b9cfc8;border-radius:6px;font-size:15px}button{background:#0f5c4d;color:#fff;border:0;cursor:pointer;margin-top:10px}button.d{background:#c0392b;width:auto;padding:4px 10px;margin:0;font-size:13px}table{width:100%;border-collapse:collapse;font-size:14px}th,td{text-align:left;padding:7px;border-bottom:1px solid #e2ece8}.bar{background:#e2ece8;border-radius:6px;height:10px;overflow:hidden}.bar i{display:block;height:100%;background:#0f5c4d}.bar i.o{background:#c0392b}.msg{background:#fff4d6;padding:10px;border-radius:6px;margin-bottom:12px}.box{max-width:380px;margin:60px auto}.tbl{overflow-x:auto}</style>";
static void head(FILE *f,const char *code,const char *hdr){fprintf(f,"HTTP/1.1 %s\r\nContent-Type: text/html; charset=utf-8\r\n%sX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n",code,hdr?hdr:"");fprintf(f,"<!doctype html><html lang=en><head><meta charset=utf-8><meta name=viewport content=\"width=device-width,initial-scale=1\"><title>Equilibrium</title>%s</head><body>",CSS);}
static void redirect(FILE *f,const char *loc,const char *extra){fprintf(f,"HTTP/1.1 303 See Other\r\nLocation: %s\r\n%sContent-Length: 0\r\nConnection: close\r\n\r\n",loc,extra?extra:"");}
static void msgbox(FILE *f,const char *q){const char *e=strstr(q,"e=");if(e){int n=atoi(e+2);if(n>0&&n<10)fprintf(f,"<div class=msg>%s</div>",MSG[n]);}}
static void page_login(FILE *f,const char *q){head(f,"200 OK",NULL);fputs("<div class=box><div class=card><h1 style=\"color:#0f5c4d;margin-top:0\">&#9878; Equilibrium</h1><p>Personal Expense &amp; Budget Tracker</p>",f);msgbox(f,q);fputs("<form method=post action=/login><label>Username</label><input name=u required maxlength=20><label>Password</label><input name=p type=password required maxlength=64><button>Log in</button></form></div><div class=card><b>New here? Create an account</b><form method=post action=/register><label>Username (3-20 letters/numbers/_)</label><input name=u required maxlength=20><label>Password (min 6)</label><input name=p type=password required minlength=6 maxlength=64><button>Register</button></form></div></div></body></html>",f);}
static void hdr_bar(FILE *f,const char *u,int admin){fprintf(f,"<header><h1>&#9878; Equilibrium</h1><div><span>Hi, ");esc(f,u);fputs("</span>",f);if(admin)fputs("<a href=/admin>Admin</a>",f);fputs("<a href=/app>Dashboard</a><a href=/logout>Logout</a></div></header><main>",f);}
static void page_app(FILE *f,const char *u,int admin,const char *q){
 int n=load(u);double bud[NC],spent[NC]={0},inc=0,exp=0;load_bud(u,bud);char mon[8],today[12];time_t now=time(NULL);struct tm tm;localtime_r(&now,&tm);strftime(mon,sizeof mon,"%Y-%m",&tm);strftime(today,sizeof today,"%Y-%m-%d",&tm);
 for(int i=0;i<n;i++){if(TX[i].type=='I')inc+=TX[i].amt;else{exp+=TX[i].amt;int c=cat_idx(TX[i].cat);if(c>=0&&!strncmp(TX[i].date,mon,7))spent[c]+=TX[i].amt;}}
 head(f,"200 OK",NULL);hdr_bar(f,u,admin);msgbox(f,q);
 fprintf(f,"<div class=grid><div class=card>Income<div class='stat inc'>&#8377;%.2f</div></div><div class=card>Expenses<div class='stat exp'>&#8377;%.2f</div></div><div class=card>Balance<div class=stat>&#8377;%.2f</div></div></div>",inc,exp,inc-exp);
 fprintf(f,"<div class=grid><div class=card><b>Add transaction</b><form method=post action=/add><label>Type</label><select name=type><option value=E>Expense</option><option value=I>Income</option></select><label>Category</label><select name=cat>");
 for(int i=0;i<NC;i++)fprintf(f,"<option>%s</option>",CATS[i]);
 fprintf(f,"</select><label>Amount (&#8377;)</label><input name=amt type=number step=0.01 min=0.01 max=999999999 required><label>Date</label><input name=date type=date value=%s required><label>Note</label><input name=note maxlength=60><button>Add</button></form></div>",today);
 fprintf(f,"<div class=card><b>Monthly budgets (%s)</b><form method=post action=/budget><label>Category</label><select name=cat>",mon);
 for(int i=0;i<NC;i++)fprintf(f,"<option>%s</option>",CATS[i]);
 fputs("</select><label>Monthly limit (&#8377;, 0 to remove)</label><input name=amt type=number step=0.01 min=0 max=999999999 required><button>Set budget</button></form>",f);
 for(int i=0;i<NC;i++)if(bud[i]>0){double p=spent[i]/bud[i]*100;fprintf(f,"<p style=margin:10px+0+2px>%s: &#8377;%.0f / &#8377;%.0f</p><div class=bar><i class='%s' style=width:%.0f%%></i></div>%s",CATS[i],spent[i],bud[i],p>100?"o":"",p>100?100:p,p>100?"<small class=exp>Over budget!</small>":"");}
 fputs("</div></div><div class=card><b>Transactions</b><div class=tbl><table><tr><th>Date<th>Type<th>Category<th>Amount<th>Note<th></tr>",f);
 for(int i=n-1;i>=0;i--){fprintf(f,"<tr><td>%s<td>%s<td>%s<td class=%s>&#8377;%.2f<td>",TX[i].date,TX[i].type=='I'?"Income":"Expense",TX[i].cat,TX[i].type=='I'?"inc":"exp",TX[i].amt);esc(f,TX[i].note);fprintf(f,"<td><form method=post action=/del><input type=hidden name=id value=%d><button class=d>Delete</button></form></tr>",TX[i].id);}
 if(!n)fputs("<tr><td colspan=6>No transactions yet.</tr>",f);
 fputs("</table></div></div></main></body></html>",f);}
static void page_admin(FILE *f,const char *me,const char *q){
 head(f,"200 OK",NULL);hdr_bar(f,me,1);msgbox(f,q);fputs("<div class=card><b>All users</b><div class=tbl><table><tr><th>User<th>Role<th>Transactions<th>Total expenses<th></tr>",f);
 char p[300];snprintf(p,sizeof p,"%s/users.db",DIR_);FILE *uf=fopen(p,"r");char names[300][32],roles[300][16];int cnt=0;
 if(uf){char u[32],h[80],r[16];while(cnt<300&&fscanf(uf,"%31s %79s %15s",u,h,r)==3){strcpy(names[cnt],u);strcpy(roles[cnt],r);cnt++;}fclose(uf);}
 for(int i=0;i<cnt;i++){int n=load(names[i]);double e=0;for(int j=0;j<n;j++)if(TX[j].type=='E')e+=TX[j].amt;fprintf(f,"<tr><td>");esc(f,names[i]);fprintf(f,"<td>%s<td>%d<td>&#8377;%.2f<td>",roles[i],n,e);
  if(strcmp(names[i],me)){fprintf(f,"<form method=post action=/admin/del onsubmit=\"return confirm('Delete this user and all data?')\"><input type=hidden name=u value=\"%s\"><button class=d>Delete user</button></form>",names[i]);}fputs("</tr>",f);}
 fputs("</table></div></div></main></body></html>",f);}
/* ---------- request handling ---------- */
static void handle(FILE *f,char *req,const char *body){
 char method[8]="",path[200]="";sscanf(req,"%7s %199s",method,path);char *q=strchr(path,'?');const char *qs="";if(q){*q=0;qs=q+1;}
 char tok[40]="";char *c=strcasestr(req,"\r\nCookie:");if(c){char *s=strstr(c,"sid=");if(s){size_t i=0;s+=4;while(*s&&*s!=';'&&*s!='\r'&&i<32)tok[i++]=*s++;tok[i]=0;}}
 const char *user=sess_user(tok);char role[16]="user";if(user)find_user(user,NULL,role);else{}
 if(user&&!find_user(user,NULL,role))user=NULL;
 int admin=user&&!strcmp(role,"admin");int post=!strcmp(method,"POST");
 char a[128],b[128],cat[32],note[128],typ[8],date[16];
 if(!strcmp(path,"/")){if(user)redirect(f,"/app",NULL);else page_login(f,qs);return;}
 if(!strcmp(path,"/healthz")){fputs("HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nok",f);return;}
 if(post&&!strcmp(path,"/login")){field(body,"u",a,sizeof a);field(body,"p",b,sizeof b);char h[80],hh[65],r[16];phash(a,b,hh);if(valid_user(a)&&find_user(a,h,r)&&!strcmp(h,hh)){Sess *s=&S[ns++%256];newtok(s->tok);snprintf(s->user,sizeof s->user,"%.20s",a);char ck[160];snprintf(ck,sizeof ck,"Set-Cookie: sid=%s; HttpOnly; SameSite=Lax; Path=/%s\r\n",s->tok,getenv("COOKIE_SECURE")?"; Secure":"");redirect(f,"/app",ck);}else redirect(f,"/?e=1",NULL);return;}
 if(post&&!strcmp(path,"/register")){field(body,"u",a,sizeof a);field(body,"p",b,sizeof b);if(!valid_user(a)){redirect(f,"/?e=2",NULL);return;}if(strlen(b)<6){redirect(f,"/?e=3",NULL);return;}if(find_user(a,NULL,NULL)){redirect(f,"/?e=4",NULL);return;}char hh[65];phash(a,b,hh);set_user(a,hh,"user");redirect(f,"/?e=5",NULL);return;}
 if(!strcmp(path,"/logout")){for(int i=0;i<256;i++)if(tok[0]&&!strcmp(S[i].tok,tok))S[i].tok[0]=0;redirect(f,"/","Set-Cookie: sid=; Max-Age=0; Path=/\r\n");return;}
 if(!user){redirect(f,"/?e=9",NULL);return;}
 if(!strcmp(path,"/app")){page_app(f,user,admin,qs);return;}
 if(post&&!strcmp(path,"/add")){field(body,"type",typ,sizeof typ);field(body,"cat",cat,sizeof cat);field(body,"amt",a,sizeof a);field(body,"date",date,sizeof date);field(body,"note",note,sizeof note);clean(note);note[60]=0;
  double amt=strtod(a,NULL);int okd=strlen(date)==10&&isdigit((unsigned char)date[0])&&date[4]=='-'&&date[7]=='-';
  if((typ[0]!='E'&&typ[0]!='I')||cat_idx(cat)<0||!(amt>0&&amt<1e9)||!okd){redirect(f,"/app?e=6",NULL);return;}
  int n=load(user);if(n>=MAXT){redirect(f,"/app?e=8",NULL);return;}int id=1;for(int i=0;i<n;i++)if(TX[i].id>=id)id=TX[i].id+1;
  char p[300];upath(p,sizeof p,"tx",user);FILE *o=fopen(p,"a");if(o){fprintf(o,"%d|%c|%s|%.2f|%s|%s\n",id,typ[0],cat,amt,date,note);fclose(o);}redirect(f,"/app?e=7",NULL);return;}
 if(post&&!strcmp(path,"/del")){field(body,"id",a,sizeof a);int id=atoi(a);int n=load(user);char p[300],t[320];upath(p,sizeof p,"tx",user);snprintf(t,sizeof t,"%s.tmp",p);FILE *o=fopen(t,"w");if(o){for(int i=0;i<n;i++)if(TX[i].id!=id)fprintf(o,"%d|%c|%s|%.2f|%s|%s\n",TX[i].id,TX[i].type,TX[i].cat,TX[i].amt,TX[i].date,TX[i].note);fclose(o);rename(t,p);}redirect(f,"/app",NULL);return;}
 if(post&&!strcmp(path,"/budget")){field(body,"cat",cat,sizeof cat);field(body,"amt",a,sizeof a);double amt=strtod(a,NULL);int ci=cat_idx(cat);if(ci<0||amt<0||amt>=1e9){redirect(f,"/app?e=6",NULL);return;}double bud[NC];load_bud(user,bud);bud[ci]=amt;char p[300];upath(p,sizeof p,"bud",user);FILE *o=fopen(p,"w");if(o){for(int i=0;i<NC;i++)if(bud[i]>0)fprintf(o,"%s %.2f\n",CATS[i],bud[i]);fclose(o);}redirect(f,"/app?e=7",NULL);return;}
 if(!strncmp(path,"/admin",6)){if(!admin){redirect(f,"/app?e=9",NULL);return;}
  if(!strcmp(path,"/admin")){page_admin(f,user,qs);return;}
  if(post&&!strcmp(path,"/admin/del")){field(body,"u",a,sizeof a);if(valid_user(a)&&strcmp(a,user))del_user(a);redirect(f,"/admin?e=7",NULL);return;}}
 fputs("HTTP/1.1 404 Not Found\r\nContent-Length: 9\r\nConnection: close\r\n\r\nNot found",f);}
int main(void){
 signal(SIGPIPE,SIG_IGN);signal(SIGCHLD,SIG_IGN);
 if(getenv("DATA_DIR"))snprintf(DIR_,sizeof DIR_,"%s",getenv("DATA_DIR"));
 mkdir(DIR_,0700);
 const char *au=getenv("ADMIN_USER"),*ap=getenv("ADMIN_PASS");
 if(au&&ap&&valid_user(au)&&strlen(ap)>=6){snprintf(ADMIN_U,sizeof ADMIN_U,"%s",au);char h[65];phash(au,ap,h);set_user(au,h,"admin");}
 else{fprintf(stderr,"Set ADMIN_USER and ADMIN_PASS (min 6 chars) environment variables.\n");return 1;}
 int port=getenv("PORT")?atoi(getenv("PORT")):8080;
 int s=socket(AF_INET,SOCK_STREAM,0),one=1;setsockopt(s,SOL_SOCKET,SO_REUSEADDR,&one,sizeof one);
 struct sockaddr_in ad={0};ad.sin_family=AF_INET;ad.sin_addr.s_addr=INADDR_ANY;ad.sin_port=htons((unsigned short)port);
 if(bind(s,(struct sockaddr*)&ad,sizeof ad)<0||listen(s,64)<0){perror("bind");return 1;}
 printf("Equilibrium listening on port %d\n",port);fflush(stdout);
 for(;;){int c=accept(s,NULL,NULL);if(c<0)continue;
  struct timeval tv={5,0};setsockopt(c,SOL_SOCKET,SO_RCVTIMEO,&tv,sizeof tv);
  static char buf[20000];size_t len=0;char *hend=NULL;int cl=0;
  while(len<sizeof buf-1){ssize_t r=recv(c,buf+len,sizeof buf-1-len,0);if(r<=0)break;len+=(size_t)r;buf[len]=0;hend=strstr(buf,"\r\n\r\n");if(hend){char *p=strcasestr(buf,"\r\nContent-Length:");cl=p&&p<hend?atoi(p+17):0;if(cl<0||cl>8000)cl=0;if(len>=(size_t)(hend+4-buf)+(size_t)cl)break;}}
  if(hend){FILE *f=fdopen(c,"w");if(f){handle(f,buf,hend+4);fclose(f);continue;}}
  close(c);}
}
