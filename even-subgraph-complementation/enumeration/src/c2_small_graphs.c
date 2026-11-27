/* Third program. Straight from the matrix form of c_2, no parametrisation:
   for every labelled graph on n <= 7 vertices, c_2 = min over diagonals D of rank(A+D) + [A+D non-zero with zero diagonal].
   Counts minimal forbidden induced subgraphs for c_2 <= k (labelled), k = 1, 2, 3, by number of vertices. */
#include <stdio.h>
#include <stdlib.h>
static int n; static unsigned char *tab[8];
static int rk(const unsigned *rows,int m){ unsigned b[8]; int r=0; for(int i=0;i<m;i++){ unsigned x=rows[i]; for(int t=0;t<r;t++){ unsigned y=x^b[t]; if(y<x) x=y; } if(x) b[r++]=x; } return r; }
static int pos(int i,int j,int m){ /* i<j, index of edge among pairs of m vertices */ int p=0; for(int a=0;a<i;a++) p+=m-1-a; return p+(j-i-1); }
int main(void){ tab[0]=calloc(1,1);
  for(n=1;n<=7;n++){ int E=n*(n-1)/2; long G=1L<<E; tab[n]=malloc(G); long cntmin[4]={0};
    for(long g=0;g<G;g++){ unsigned A[8]={0}; for(int i=0;i<n;i++)for(int j=i+1;j<n;j++) if(g>>pos(i,j,n)&1){A[i]|=1u<<j;A[j]|=1u<<i;}
      int best=99; for(unsigned D=0;D<(1u<<n);D++){ unsigned B[8]; for(int i=0;i<n;i++) B[i]=A[i]^(D&(1u<<i)); int r=rk(B,n); int f=r+((D==0&&g!=0)?1:0); if(f<best) best=f; }
      tab[n][g]=best;
      int submax=0; for(int d=0;d<n;d++){ long h=0; int ii=0; for(int i=0;i<n;i++){ if(i==d) continue; int jj=ii+1; for(int j=i+1;j<n;j++){ if(j==d) continue; if(g>>pos(i,j,n)&1) h|=1L<<pos(ii,jj,n-1); jj++; } ii++; }
        int c=(n>1)?tab[n-1][h]:0; if(c>submax) submax=c; }
      for(int k=1;k<=3;k++) if(best>k && submax<=k) cntmin[k]++; }
    printf("n=%d labelled graphs=%ld  minimal forbidden for c_2<=1: %ld   c_2<=2: %ld   c_2<=3: %ld\n",n,G,cntmin[1],cntmin[2],cntmin[3]); fflush(stdout); }
  return 0; }
