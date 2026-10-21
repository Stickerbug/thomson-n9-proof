"""Stable proposal evaluator of exact old residual budget; exact points available."""
import json
from fractions import Fraction as F
import numpy as np
import mpmath as mp
from sharp_contact_refinement2026_core import ROOT
from sharp_contact_refinement2026_competitive import Competitive

class KernelBudget:
    def __init__(self):
        self.model=json.loads((ROOT/'nonsharp_d10_root25_7599205_v10.json').read_text());upper=json.loads((ROOT/'pair056_optimized_certificate.json').read_text());self.budget=7*(F(upper['U'])-F(self.model['target']));self.terms=self.model['residual_monomial'];self.powers=np.array([e for e,s in self.terms],dtype=int)
        def ld(q):q=F(q);return np.longdouble(str(q.numerator))/np.longdouble(str(q.denominator))
        self.coefficients=np.array([ld(s) for e,s in self.terms],dtype=np.longdouble);self.constant=ld(self.budget);self.maxdegree=int(self.powers.max())
    def __call__(self,points,grad=False):
        points=np.atleast_2d(points);values=[];grads=[]
        for start in range(0,len(points),512):
            p=np.asarray(points[start:start+512],dtype=np.longdouble);pw=[p[:,i,None]**np.arange(self.maxdegree+1) for i in range(3)];monomial=np.ones((len(p),len(self.powers)),dtype=np.longdouble)
            for i in range(3):monomial*=pw[i][:,self.powers[:,i]]
            values.append(np.asarray(self.constant-monomial@self.coefficients,dtype=float))
            if grad:
                g=[]
                for axis in range(3):
                    m=np.ones_like(monomial)
                    for i in range(3):m*=pw[i][:,np.maximum(0,self.powers[:,i]-(i==axis))]
                    g.append(np.asarray(-m@(self.coefficients*self.powers[:,axis]),dtype=float))
                grads.append(np.column_stack(g))
        v=np.concatenate(values);return (v,np.vstack(grads)) if grad else v
    def exact_fraction(self,point):
        p=[F(str(v)) for v in point];return self.budget-sum(F(s)*p[0]**e[0]*p[1]**e[1]*p[2]**e[2] for e,s in self.terms)
    def exact_decimal_value(self,point):
        v=self.exact_fraction(point);return mp.nstr(mp.mpf(v.numerator)/v.denominator,80)

class JointBudget:
    def __init__(self):
        self.C=Competitive(json.loads((ROOT/'competitive_triple_constraint_certificate.json').read_text()));self.K=KernelBudget()
    def __call__(self,points):return np.minimum(self.C(points),self.K(points))
