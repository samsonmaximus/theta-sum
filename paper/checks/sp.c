/* sp.c: a second, separately written implementation of S(p) by the counting formula
   (Lemma 9.1 of paper/theta_sum_conj33.pdf), used for check (ii) of Section 9.2 on the
   primes 4e6 < p <= 6e6. Output lines "p S(p)" are compared with the data file by
   compare_recompute.py.
   Build: gcc -O2 -o sp sp.c
   Run:   ./sp p1 p2 ... > out_<name>.txt     (S(p) for each given odd prime p)
          ./sp b p                            (S(p) from the definition, O(p^2))       */
#include <stdio.h>
#include <stdlib.h>
typedef __int128 i128;
/* W(x,y)=sum_{c=1}^{floor((y-1)/2)} floor(c x / y), gcd(x,y)=1 */
static i128 W(long long x,long long y){
  i128 sign=1, acc=0;
  while(1){
    if(y<=2) return acc; /* A=0 */
    long long A=(y-1)/2;
    long long q=x/y, r=x%y;
    acc += sign*(i128)q*A*(A+1)/2;
    if(r==0) return acc;
    long long B=(r-1)/2;
    acc += sign*(i128)A*B;   /* W(r,y)=AB-W(y,r) */
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
    i128 t=0; for(long long a=3;a<=p-2;a+=2) t+=W(2*p,a);
    i128 S=(i128)(p-1)*(p-1)*(p-1)/4 - 4*t;
    printf("%lld %lld\n",p,(long long)S);
  }
}
