/* First program. Independent of the proof.
   Every graph whose adjacency matrix has rank 4 over F_2 is U J U^T with rows of U in F_2^4
   and J the standard symplectic form (all non-singular alternating forms are congruent),
   so such graphs on n vertices = multisets of n vectors of F_2^4 that span.
   For each: brute force over ALL diagonals D.
     obstruction  : rank(A + D) >= 5 for every D != 0   (then c_2 = 5 > 4, as rank A = 4, zero diagonal)
     minimal      : for every vertex v, c_2(G - v) <= 4, i.e. rank A_v <= 2, or some D != 0 with rank(A_v + D) <= 4
   Output: counts by n, and whether each minimal obstruction is 'tripled' (4 distinct independent vectors, each 3 times).
   usage: ./a.out n nproc */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
static int n, W[16][16], v[20];
static unsigned *masks; static int nmask;
static long cnt_all, cnt_span, cnt_obs, cnt_min, cnt_trip, cnt_min_nontrip;
static int me, nproc; static long leafctr;
static inline int rank_cap(const unsigned *rows, int m, int cap){
  unsigned b[8]; int r=0;
  for(int i=0;i<m;i++){ unsigned x=rows[i];
    for(int t=0;t<r;t++){ unsigned y=x^b[t]; if(y<x) x=y; }
    if(x){ if(r==cap) return cap+1; b[r++]=x; } }
  return r; }
static int cmpmask(const void*a,const void*b){ unsigned x=*(unsigned*)a,y=*(unsigned*)b;
  int px=__builtin_popcount(x),py=__builtin_popcount(y); if(px!=py) return px-py; return (x>y)-(x<y); }
static void leaf(void){
  cnt_all++;
  unsigned sp[1]; unsigned vv[20]; for(int i=0;i<n;i++) vv[i]=v[i];
  if(rank_cap(vv,n,4)!=4) return; (void)sp;
  cnt_span++;
  unsigned A[20], B[20];
  for(int i=0;i<n;i++){ unsigned r=0; for(int j=0;j<n;j++) if(W[v[i]][v[j]]) r|=1u<<j; A[i]=r; }
  for(int t=0;t<nmask;t++){ unsigned D=masks[t];
    for(int i=0;i<n;i++) B[i]=A[i]^(D&(1u<<i));
    if(rank_cap(B,n,4)<=4) return; }
  cnt_obs++;
  int minimal=1;
  for(int d=0;d<n && minimal;d++){
    unsigned keep=~(1u<<d); unsigned Av[20];
    for(int i=0;i<n;i++) Av[i]=(i==d)?0:(A[i]&keep);
    int ok = rank_cap(Av,n,4)<=2;
    for(int t=0;t<nmask && !ok;t++){ unsigned D=masks[t]; if(D&(1u<<d)) continue;
      for(int i=0;i<n;i++) B[i]=Av[i]^(D&(1u<<i));
      if(rank_cap(B,n,4)<=4) ok=1; }
    if(!ok) minimal=0; }
  if(!minimal) return;
  cnt_min++;
  int mult[16]={0}; for(int i=0;i<n;i++) mult[v[i]]++;
  int trip=(n==12); int distinct=0; for(int a=0;a<16;a++){ if(mult[a]){ distinct++; if(mult[a]!=3) trip=0; } }
  if(distinct!=4||mult[0]) trip=0;
  if(trip) cnt_trip++; else { cnt_min_nontrip++;
    printf("MINIMAL-NOT-TRIPLED n=%d:",n); for(int i=0;i<n;i++) printf(" %d",v[i]); printf("\n"); fflush(stdout);} }
static void rec(int pos,int lo){
  if(pos==3||(n<3&&pos==n)){ if((leafctr++ % nproc)!=me) return; }
  if(pos==n){ leaf(); return; }
  for(int a=lo;a<16;a++){ v[pos]=a; rec(pos+1,a); } }
int main(int argc,char**argv){
  n=atoi(argv[1]); nproc=atoi(argv[2]);
  for(int a=0;a<16;a++)for(int b=0;b<16;b++){ int a0=a&1,a1=(a>>1)&1,a2=(a>>2)&1,a3=(a>>3)&1,b0=b&1,b1=(b>>1)&1,b2=(b>>2)&1,b3=(b>>3)&1;
    W[a][b]=(a0&b1)^(a1&b0)^(a2&b3)^(a3&b2); }
  nmask=(1<<n)-1; masks=malloc(sizeof(unsigned)*nmask); for(int i=0;i<nmask;i++) masks[i]=i+1; qsort(masks,nmask,sizeof(unsigned),cmpmask);
  int fd[8][2];
  for(me=0;me<nproc;me++){ pipe(fd[me]); if(fork()==0){ leafctr=0; rec(0,0);
      long out[6]={cnt_all,cnt_span,cnt_obs,cnt_min,cnt_trip,cnt_min_nontrip}; write(fd[me][1],out,sizeof out); _exit(0);} }
  long tot[6]={0}; for(int c=0;c<nproc;c++){ long out[6]; read(fd[c][0],out,sizeof out); for(int i=0;i<6;i++) tot[i]+=out[i]; }
  while(wait(NULL)>0);
  printf("n=%d multisets=%ld spanning(rank A=4)=%ld obstructions(c2=5)=%ld minimal=%ld tripled=%ld minimal_not_tripled=%ld\n",n,tot[0],tot[1],tot[2],tot[3],tot[4],tot[5]);
  return 0; }
