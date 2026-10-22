#include <stdint.h>
#include <stddef.h>
#include <string.h>
/* Signed values are transferred by memcpy, never by aliasing or signed shifts. */
typedef __int128 i128;
static const i128 LIM=((i128)1)<<124;
static i128 load(const uint64_t *p){i128 x;memcpy(&x,p,16);return x;}
static void store(uint64_t *p,i128 x){memcpy(p,&x,16);}
static int inside(i128 x){return x>-LIM && x<LIM;}
int exact128_layout(void){i128 x=-1;unsigned char b[16];uint16_t y=1;
 if(sizeof(i128)!=16 || sizeof(uint64_t)!=8 || *(unsigned char*)&y!=1)return 0;
 memcpy(b,&x,16);for(int j=0;j<16;j++)if(b[j]!=255)return 0;return 1;}
int exact128_minmax(const uint64_t *src,uint64_t count,uint64_t *lo,uint64_t *hi){
 if(!src||!lo||!hi||!count||count>262144)return 1;
 i128 a=load(src),b=a;if(!inside(a))return 2;
 for(uint64_t j=1;j<count;j++){i128 x=load(src+2*j);if(!inside(x))return 2;if(x<a)a=x;if(x>b)b=x;}
 store(lo,a);store(hi,b);return 0;}
int exact128_split(const uint64_t *src,uint64_t *left,uint64_t *right,
 const uint64_t *dims,uint64_t count,int axis,int upper){
 if(!src||!left||!right||!dims||axis<0||axis>2||(upper!=0&&upper!=1))return 1;
 uint64_t total=1,stride=1;
 for(int j=0;j<3;j++){if(!dims[j]||dims[j]>64)return 1;total*=dims[j];if(j>axis)stride*=dims[j];}
 if(total!=count)return 1;
 /* Reject before any output write; arithmetic later stays inside signed128. */
 for(uint64_t j=0;j<count;j++)if(!inside(load(src+2*j)))return 2;
 uint64_t n=dims[axis],block=n*stride;
 for(uint64_t base=0;base<total;base+=block)for(uint64_t off=0;off<stride;off++){
  i128 row[64];for(uint64_t j=0;j<n;j++)row[j]=load(src+2*(base+off+j*stride));
  store(left+2*(base+off),row[0]);store(right+2*(base+off+(n-1)*stride),row[n-1]);
  for(uint64_t level=1;level<n;level++){
   for(uint64_t j=0;j<n-level;j++){
    i128 s=row[j]+row[j+1]+upper; /* |s|<2^125+1, safely within signed128. */
    i128 z=s/2;if(s<0 && s%2!=0)z--;row[j]=z;
   }
   store(left+2*(base+off+level*stride),row[0]);
   store(right+2*(base+off+(n-1-level)*stride),row[n-1-level]);
  }
 }
 return 0;
}
