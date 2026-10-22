#include <stdint.h>
#include <string.h>
static __int128 load(const uint64_t*p){__int128 v;memcpy(&v,p,16);return v;}
int analytic10_min(const uint64_t*b,const uint64_t*x,const uint64_t*y,const uint64_t*z,uint64_t*out){
const __int128 L=((__int128)1)<<124,M=((__int128)1)<<126;__int128 xx[11],yy[11],zz[11],best=M;
for(int i=0;i<11;i++){xx[i]=load(x+2*i);yy[i]=load(y+2*i);zz[i]=load(z+2*i);if(xx[i]<=-L||xx[i]>=L||yy[i]<=-L||yy[i]>=L||zz[i]<=-L||zz[i]>=L)return 2;}
for(int i=0;i<11;i++)for(int j=0;j<11;j++)for(int k=0;k<11;k++){__int128 v=load(b+2*((i*11+j)*11+k));if(v<=-L||v>=L)return 2;__int128 a=v+xx[i]+yy[j]+zz[k];if(a<=-M||a>=M)return 3;if(a<best)best=a;}
memcpy(out,&best,16);return 0;}
