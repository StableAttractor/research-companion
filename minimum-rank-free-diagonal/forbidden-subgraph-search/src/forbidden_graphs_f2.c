// Used in the note only for c(G) = mr(F_2, G) (the "lines X, Y" invariant below). The other invariant in this file is not used.
// Over F_2. Graph G on n vertices. Two invariants:
//  rho(G) = min over one of three lines per vertex (X: row of A; Y: row of A + e_i; Z: e_i) of the rank  [Pauli persistency]
//  c(G)   = same with X, Y only                                                                    [minimum rank over F_2, free diagonal]
// Minimal obstruction for k: invariant(G) >= k+1 and invariant(G - v) <= k for every vertex v.
// Exact tables for all labelled graphs on n <= 7 vertices; n = 8 scanned exhaustively through the 7-vertex table.
// Graph code: bit index of pair (i<j) is j(j-1)/2 + i, so the graph minus its last vertex is the low bits.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static inline int rk(uint32_t *a,int m){int r=0;for(int i=0;i<m;i++){if(!a[i])continue;uint32_t low=a[i]&-a[i];r++;for(int t=i+1;t<m;t++)if(a[t]&low)a[t]^=a[i];}return r;}
static void adj_of(uint32_t code,int n,uint32_t*A){for(int i=0;i<n;i++)A[i]=0;int b=0;for(int j=1;j<n;j++)for(int i=0;i<j;i++,b++)if(code>>b&1){A[i]|=1u<<j;A[j]|=1u<<i;}}
static uint32_t code_of(uint32_t*A,int n,int skip){uint32_t c=0;int b=0;int id[9],m=0;for(int i=0;i<n;i++)if(i!=skip)id[m++]=i;for(int j=1;j<m;j++)for(int i=0;i<j;i++,b++)if(A[id[i]]>>id[j]&1)c|=1u<<b;return c;}
static int inv(uint32_t*A,int n,int lines,int stop){ // lines = 3 (rho) or 2 (c); stop: return early if value <= stop
  int best=n; int d[9]={0}; uint32_t rows[9];
  for(;;){ for(int i=0;i<n;i++)rows[i]= d[i]==0?A[i]: d[i]==1?(A[i]|1u<<i):(1u<<i);
    int v=rk(rows,n); if(v<best){best=v;if(best<=stop)return best;}
    int i=0; while(i<n){ if(++d[i]<lines)break; d[i]=0;i++; } if(i==n)break; }
  return best; }
static uint8_t *T[2][9]; static uint32_t F8[100000];
static uint32_t canon(uint32_t code,int n){ int p[9];for(int i=0;i<n;i++)p[i]=i; uint32_t A[9];adj_of(code,n,A); uint32_t best=0xffffffffu;
  // all permutations (Heap)
  int c[9]={0}; for(;;){ uint32_t cc=0;int b=0;for(int j=1;j<n;j++)for(int i=0;i<j;i++,b++)if(A[p[i]]>>p[j]&1)cc|=1u<<b; if(cc<best)best=cc;
    int i=1; while(i<n){ if(c[i]<i){ int a=(i&1)?c[i]:0; int t=p[a];p[a]=p[i];p[i]=t; c[i]++; break;} c[i]=0;i++; } if(i>=n)break; }
  return best; }
static int cmpu(const void*a,const void*b){uint32_t x=*(uint32_t*)a,y=*(uint32_t*)b;return x<y?-1:x>y;}
int main(){
  const char*nm[2]={"rho (Pauli persistency, lines X,Y,Z)","c (minimum rank over F_2, lines X,Y)"};
  for(int w=0;w<2;w++){ T[w][0]=calloc(1,1); T[w][1]=calloc(1,1); }
  for(int n=2;n<=7;n++){ uint32_t NG=1u<<(n*(n-1)/2); for(int w=0;w<2;w++)T[w][n]=malloc(NG);
    for(uint32_t g=0;g<NG;g++){uint32_t A[9];adj_of(g,n,A);T[0][n][g]=0;T[1][n][g]=inv(A,n,2,-1);} fprintf(stderr,"tables n=%d done\n",n); }
  for(int w=1;w<2;w++){ printf("== %s\n",nm[w]);
    for(int k=1;k<=3;k++){ printf(" k=%d (2k+2=%d):\n",k,2*k+2);
      for(int n=2;n<=7;n++){ uint32_t NG=1u<<(n*(n-1)/2); long cnt=0; uint32_t *found=NULL; long cap=0;
        for(uint32_t g=0;g<NG;g++){ if(T[w][n][g]<k+1)continue; uint32_t A[9];adj_of(g,n,A); int ok=1; for(int v=0;v<n&&ok;v++){ if(n-1>=2){ if(T[w][n-1][code_of(A,n,v)]>k)ok=0; } }
          if(ok){ if(cnt==cap){cap=cap?cap*2:1024;found=realloc(found,cap*sizeof(uint32_t));} found[cnt++]=g; } }
        if(!cnt){ printf("  n=%d: none\n",n); continue; }
        long ncan=-1; if(cnt<=400000){ for(long i=0;i<cnt;i++)found[i]=canon(found[i],n); qsort(found,cnt,sizeof(uint32_t),cmpu); ncan=0; for(long i=0;i<cnt;i++)if(!i||found[i]!=found[i-1])found[ncan++]=found[i]; }
        printf("  n=%d: %ld labelled",n,cnt); if(ncan>=0){ printf(", %ld up to isomorphism",ncan); if(ncan<=40){ printf(":"); for(long i=0;i<ncan;i++){ uint32_t A[9];adj_of(found[i],n,A); printf(" {"); int first=1; for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)if(A[a]>>b&1){printf("%s%d%d",first?"":",",a,b);first=0;} printf("}"); } } } printf("\n"); free(found); } } }
  // n = 8 exhaustive through the 7-vertex tables: any minimal obstruction for k <= 2 ?
  for(int w=1;w<2;w++) for(int k=3;k<=3;k++){ long cnt=0; uint32_t NG=1u<<28; 
    for(uint32_t g=0;g<NG;g++){ if(T[w][7][g&((1u<<21)-1)]>k)continue; uint32_t A[9];adj_of(g,8,A); int ok=1; for(int v=0;v<7&&ok;v++) if(T[w][7][code_of(A,8,v)]>k)ok=0; if(!ok)continue;
      if(inv(A,8,w?2:3,k)>=k+1){ if(k==3&&cnt<100000)F8[cnt]=g; cnt++; } }
    if(k==3){ for(long i=0;i<cnt;i++)F8[i]=canon(F8[i],8); qsort(F8,cnt,sizeof(uint32_t),cmpu); long nc=0; for(long i=0;i<cnt;i++)if(!i||F8[i]!=F8[i-1])F8[nc++]=F8[i]; printf("n=8 c k=3: %ld up to isomorphism:",nc); for(long i=0;i<nc;i++){ uint32_t A[9];adj_of(F8[i],8,A); printf(" {"); int first=1; for(int a=0;a<8;a++)for(int b=a+1;b<8;b++)if(A[a]>>b&1){printf("%s%d%d",first?"":",",a,b);first=0;} printf("}"); } printf("\n"); }
    printf("n=8, %s, k=%d: minimal obstructions (labelled): %ld%s\n",w?"c":"rho",k,cnt,(2*k+2<8)?"   [theorem predicts 0]":""); fflush(stdout); }
  return 0; }
