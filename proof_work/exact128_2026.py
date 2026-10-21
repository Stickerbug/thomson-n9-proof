"""Range-guarded signed128 exact Bernstein tensors. No scale conversions."""
import ctypes as C
import hashlib,subprocess,sys,numbers
from pathlib import Path
import numpy as np
LIMIT=1<<124
ROOT=Path(__file__).resolve().parent
_LIB=None

def library():
 global _LIB
 if _LIB is not None:return _LIB
 if sys.byteorder!='little' or C.sizeof(C.c_uint64)!=8:raise RuntimeError('Native backend requires little-endian64-bit words')
 src=ROOT/'exact128_2026.c';tag=hashlib.sha256(src.read_bytes()).hexdigest()[:16];so=ROOT/f'exact128_2026_{tag}.so'
 if not so.exists():subprocess.run(['/usr/bin/gcc','-O2','-std=gnu11','-shared','-fPIC',str(src),'-o',str(so)],check=True)
 lib=C.CDLL(str(so));ptr=C.POINTER(C.c_uint64)
 lib.exact128_layout.argtypes=[];lib.exact128_layout.restype=C.c_int
 if lib.exact128_layout()!=1:raise RuntimeError('Unsupported signed128 byte layout')
 lib.exact128_minmax.argtypes=[ptr,C.c_uint64,ptr,ptr];lib.exact128_minmax.restype=C.c_int
 lib.exact128_split.argtypes=[ptr,ptr,ptr,ptr,C.c_uint64,C.c_int,C.c_int];lib.exact128_split.restype=C.c_int
 _LIB=lib;return lib

def pointer(a):return a.ctypes.data_as(C.POINTER(C.c_uint64))
def check(code):
 if code==2:raise OverflowError('Native tensor requires strict abs(value)<2^124')
 if code:raise ValueError('Invalid native tensor shape/count/axis/rounding mode')
def decode(a):return int.from_bytes(a.tobytes(),'little',signed=True)

class NativeTensor:
 dtype='signed128-native'
 def __init__(self,values):
  a=np.asarray(values,dtype=object)
  if a.ndim!=3 or any(n<1 or n>64 for n in a.shape):raise ValueError('Need a3D tensor with each dimension in1..64')
  raw=bytearray()
  for v in a.flat:
   if isinstance(v,(bool,np.bool_))or not isinstance(v,numbers.Integral):raise TypeError('Exact integer values required')
   x=int(v)
   if not -LIMIT<x<LIMIT:raise OverflowError('Native tensor requires strict abs(value)<2^124')
   raw.extend(x.to_bytes(16,'little',signed=True))
  library();self._words=np.frombuffer(raw,dtype=np.uint64).reshape(a.shape+(2,));self.shape=a.shape
 @classmethod
 def _wrap(cls,words):
  o=cls.__new__(cls);o._words=words;o.shape=words.shape[:-1];return o
 def _minmax(self):
  lo=np.empty(2,dtype=np.uint64);hi=np.empty(2,dtype=np.uint64)
  check(library().exact128_minmax(pointer(self._words),self._words.size//2,pointer(lo),pointer(hi)))
  return decode(lo),decode(hi)
 def min(self):return self._minmax()[0]
 def max(self):return self._minmax()[1]
 def split(self,axis,upper=False):
  if isinstance(axis,bool)or not isinstance(axis,numbers.Integral)or not 0<=axis<3:raise ValueError('axis must be0,1,2')
  if upper not in (False,True,0,1):raise ValueError('upper must be0 or1')
  left=np.empty_like(self._words);right=np.empty_like(self._words);dims=np.array(self.shape,dtype=np.uint64)
  check(library().exact128_split(pointer(self._words),pointer(left),pointer(right),pointer(dims),self._words.size//2,int(axis),int(upper)))
  return self._wrap(left),self._wrap(right)
 def to_object(self):
  out=np.empty(self.shape,dtype=object)
  for index in np.ndindex(self.shape):out[index]=decode(self._words[index])
  return out

def split(tensor,axis,upper=False):return tensor.split(axis,upper)
