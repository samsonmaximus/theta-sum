#include <stdio.h>
#include <stdlib.h>
typedef __int128 i128;
/* F(x,y)=sum_{c=1}^{floor((y-1)/2)} floor(c x / y), gcd(x,y)=1 */
static i128 F(long long x,long long y){
  i128 sign=1, acc=0;
  while(1){
    if(y<=2) return acc; /* U=0 */
    long long U=(y-1)/2;
    long long q=x/y, r=x%y;
    acc += sign*(i128)q*U*(U+1)/2;
    if(r==0) return acc;
    long long V=(r-1)/2;
    acc += sign*(i128)U*V;   /* F(r,y)=UV-F(y,r) */
    sign=-sign; x=y; y=r;
  }
}
static long long brute(long long p){
  long long s=0;
  for(long long h=1;h<p;h++)for(long long j=1;j<p;j++){long long e=j+1+(h*j)/p; s+= (e&1)?-1:1;}
  return s;
}
int main(int argc,char**argv){
  if(argc>2 && argv[1][0]=='b'){ long long p=atoll(argv[2]); printf("%lld\n",brute(p)); return 0;}
  for(int i=1;i<argc;i++){
    long long p=atoll(argv[i]);
    i128 t=0; for(long long a=3;a<=p-2;a+=2) t+=F(2*p,a);
    i128 S=(i128)(p-1)*(p-1)*(p-1)/4 - 4*t;
    printf("%lld %lld\n",p,(long long)S);
  }
}
