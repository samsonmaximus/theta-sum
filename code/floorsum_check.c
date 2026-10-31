/* floorsum_check.c: an independent check of S(p), sharing no code or method with
   thetasum.c (which uses Lemma 2.5). Write (-1)^x = 1 - 2x + 4 floor(x/2) with
   x = j+1+floor(hj/p); then floor(x/2) = floor(((h+p)j + p)/(2p)), so every inner
   sum over j is a floor sum of a linear function, evaluated in O(log p) by the
   Euclid-type algorithm. Total cost O(p log p).
   Build: gcc -O2 -o floorsum_check floorsum_check.c ; run: ./floorsum_check p1 p2 ... */
#include <stdio.h>
#include <stdlib.h>
typedef __int128 i128;
static i128 floor_sum(i128 n, i128 m, i128 a, i128 b){ /* sum_{i=0}^{n-1} floor((a i+b)/m), a,b>=0 */
  i128 ans=0;
  for(;;){
    if(a>=m){ ans+=(n-1)*n/2*(a/m); a%=m; }
    if(b>=m){ ans+=n*(b/m); b%=m; }
    i128 y=a*n+b; if(y<m) break;
    n=y/m; b=y%m; i128 t=m; m=a; a=t;
  }
  return ans;
}
int main(int argc,char**argv){
  for(int i=1;i<argc;i++){
    long long p=atoll(argv[i]); i128 S=0;
    for(long long h=1;h<p;h++){
      i128 X = floor_sum(p,1,1,1) - 1        /* sum_{j=1}^{p-1}(j+1) */
             + floor_sum(p,p,h,0);           /* sum_j floor(hj/p) */
      i128 Y = floor_sum(p,2*p,h+p,p);       /* j=0 term is 0 */
      S += (p-1) - 2*X + 4*Y;
    }
    printf("%lld %lld\n",p,(long long)S);
  }
}
