/* Second program.
   Same objects as rank4_branch_exhaustive.c: graphs with adjacency rank 4 over F_2 = spanning multisets of
   n vectors of F_2^4, adjacency U J U^T.  Level by level in n, with a table of which multisets are obstructions
   (c_2 = 5), using only that c_2 does not increase on induced subgraphs:
     G on n vertices is an obstruction  iff  some spanning G - v is one, or rank(A + D) >= 5 for all D != 0 (brute force);
     G is a MINIMAL obstruction         iff  no G - v is an obstruction and the brute-force test holds.
   (A non-spanning G - v has adjacency rank <= 2, so c_2 <= 3.)
   Cross-check: minimal counts for n <= 11 must equal those of rank4_branch_exhaustive.c, which uses no table.
   usage: ./a.out nmax */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n, W[16][16], v[24]; static uint64_t C[40][40];
static unsigned char *tab[24]; static unsigned *masks; static int nmask;
static long c_all,c_span,c_obs,c_min,c_trip,c_min_nontrip,c_brute;
static inline int rank_cap(const unsigned *rows,int m,int cap){ unsigned b[8]; int r=0;
  for(int i=0;i<m;i++){ unsigned x=rows[i]; for(int t=0;t<r;t++){ unsigned y=x^b[t]; if(y<x) x=y; }
    if(x){ if(r==cap) return cap+1; b[r++]=x; } } return r; }
static inline uint64_t idx(const int *w,int m){ uint64_t s=0; for(int i=0;i<m;i++) s+=C[w[i]+i][i+1]; return s; }
static int cmpmask(const void*a,const void*b){ unsigned x=*(unsigned*)a,y=*(unsigned*)b; int px=__builtin_popcount(x),py=__builtin_popcount(y); if(px!=py) return px-py; return (x>y)-(x<y); }
static void leaf(void){
  c_all++; unsigned vv[24]; for(int i=0;i<n;i++) vv[i]=v[i];
  if(rank_cap(vv,n,4)!=4) return; c_span++;
  uint64_t me=idx(v,n); int w[24]; int sub=0;
  for(int d=0;d<n && !sub;d++){ if(d>0&&v[d]==v[d-1]) continue; int m=0; for(int i=0;i<n;i++) if(i!=d) w[m++]=v[i];
    uint64_t j=idx(w,m); if(tab[n-1][j>>3]>>(j&7)&1) sub=1; }
  if(sub){ tab[n][me>>3]|=1<<(me&7); c_obs++; return; }
  c_brute++; unsigned A[24],B[24];
  for(int i=0;i<n;i++){ unsigned r=0; for(int j=0;j<n;j++) if(W[v[i]][v[j]]) r|=1u<<j; A[i]=r; }
  for(int t=0;t<nmask;t++){ unsigned D=masks[t]; for(int i=0;i<n;i++) B[i]=A[i]^(D&(1u<<i)); if(rank_cap(B,n,4)<=4) return; }
  tab[n][me>>3]|=1<<(me&7); c_obs++; c_min++;
  int mult[16]={0}; for(int i=0;i<n;i++) mult[v[i]]++; int trip=(n==12),distinct=0;
  for(int a=0;a<16;a++) if(mult[a]){ distinct++; if(mult[a]!=3) trip=0; } if(distinct!=4||mult[0]) trip=0;
  if(trip) c_trip++; else { c_min_nontrip++; if(n>=12){ printf("MINIMAL-NOT-TRIPLED n=%d:",n); for(int i=0;i<n;i++) printf(" %d",v[i]); printf("\n"); } } }
static void rec(int pos,int lo){ if(pos==n){ leaf(); return; } for(int a=lo;a<16;a++){ v[pos]=a; rec(pos+1,a); } }
int main(int argc,char**argv){ int nmax=atoi(argv[1]);
  for(int i=0;i<40;i++){ C[i][0]=1; for(int j=1;j<40;j++) C[i][j]= i? C[i-1][j-1]+C[i-1][j] : 0; }
  for(int a=0;a<16;a++)for(int b=0;b<16;b++){ int a0=a&1,a1=(a>>1)&1,a2=(a>>2)&1,a3=(a>>3)&1,b0=b&1,b1=(b>>1)&1,b2=(b>>2)&1,b3=(b>>3)&1; W[a][b]=(a0&b1)^(a1&b0)^(a2&b3)^(a3&b2); }
  tab[3]=calloc(C[18][3]/8+1,1);
  for(n=4;n<=nmax;n++){ tab[n]=calloc(C[15+n][n]/8+1,1); nmask=(1<<n)-1; masks=malloc(sizeof(unsigned)*nmask); for(int i=0;i<nmask;i++) masks[i]=i+1; qsort(masks,nmask,sizeof(unsigned),cmpmask);
    c_all=c_span=c_obs=c_min=c_trip=c_min_nontrip=c_brute=0; rec(0,0); free(masks);
    printf("n=%d multisets=%ld spanning(rank A=4)=%ld obstructions(c2=5)=%ld brute_force_tested=%ld minimal=%ld tripled=%ld minimal_not_tripled=%ld\n",n,c_all,c_span,c_obs,c_brute,c_min,c_trip,c_min_nontrip); fflush(stdout); }
  return 0; }
