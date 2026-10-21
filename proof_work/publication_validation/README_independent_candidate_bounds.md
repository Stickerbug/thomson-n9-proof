# Independent candidate parameter and energy bounds

The checker uses only Fraction, integer isqrt and other standard-library utilities. The sole mathematical input read from the original coefficient-model certificate is root_interval; its whole source SHA is retained for provenance. No old arithmetic, model helper or interval module is imported. The literal U is independently fixed at 25.75998653126983156407570227376049402866.

Every input and arithmetic result is rounded outwards to the dyadic grid 2^-640. Addition uses endpoint sums, subtraction uses negation, multiplication uses all four endpoint products, and reciprocal first rejects intervals containing zero and reverses reciprocal endpoints. Every constructor checks its exact rational outward enclosure. For sqrt([a,b]), integer isqrt computes L=floor(sqrt(a)*2^640) and an upper integer H with H^2/2^1280>=b. Each sqrt result explicitly checks 0<=L/2^640<=H/2^640, (L/2^640)^2<=a, and (H/2^640)^2>=b, and saves input/output intervals for audit.

For 0<r<1 write h=sqrt(1-r^2). Take three upper points (r v_k,h), three lower points (r v_k,-h), and three equatorial points (w_k,0), with

v_0=(1,0), v_1=(-1/2,sqrt(3)/2), v_2=(-1/2,-sqrt(3)/2),
w_0=(1/2,sqrt(3)/2), w_1=(-1,0), w_2=(1/2,-sqrt(3)/2).

The checker represents planar coordinates exactly in Q(sqrt(3)) and dot products as rational triples giving coefficients of 1,r,r^2, applying h^2=1-r^2. It verifies nine symbolic unit norms and enumerates all 36 unordered pairs. The dot multiplicities are

| dot | count | squared distance |
| --- | ---: | --- |
| 1-3r^2/2 | 6 | 3r^2 |
| 2r^2-1 | 3 | 4(1-r^2) |
| r^2/2-1 | 6 | 4-r^2 |
| -1/2 | 3 | 3 |
| r/2 | 12 | 2-r |
| -r | 6 | 2+2r |

Every squared distance is positive for 0<r<1, so all points are distinct. Exact rational squared-prefactor identities check simplification of each count divided by the corresponding distance. Thus the actual 36-pair Coulomb energy equals

E_D(r)=sqrt(3)+2sqrt(3)/r+(3/2)/sqrt(1-r^2)+6/sqrt(4-r^2)+12/sqrt(2-r)+6/sqrt(2+2r).

Its derivative is

E_D'(r)=-2sqrt(3)/r^2+(3/2)r/(1-r^2)^(3/2)+6r/(4-r^2)^(3/2)+6/(2-r)^(3/2)-6/(2+2r)^(3/2).

The interval computation proves E_D'(lo)<0 and E_D'(hi)>0, and evaluates the entire supplied bracket to obtain sup E_D([lo,hi])<U. It does not replace the true root by either endpoint or by a rational midpoint. The exact output records the derivative enclosures, energy enclosure, and positive rational margin U-energy_upper.

Direct differentiation gives

E_D''(r)=4sqrt(3)/r^3+(3/2)(1+2r^2)/(1-r^2)^(5/2)+6(4+2r^2)/(4-r^2)^(5/2)+9/(2-r)^(5/2)+18/(2+2r)^(5/2)>0

on (0,1), since every numerator and denominator is positive. E_D' is continuous and strictly increasing there. The intermediate value theorem and the certified strict endpoint signs imply exactly one stationary r_star in the supplied bracket, and strict convexity makes it the unique minimum of this family. The whole-bracket bound implies E_D(r_star)<U. Differentiation, continuity, IVT and the general convexity implication are written mathematical arguments, not a Lean-checked derivation.

Negative tests reject an inverted root bracket, a reciprocal across zero, an intentionally downward-rounded sqrt upper endpoint, and an energy target U=25 that lies below the computed energy. They fail by exact inequalities, not by a hash mismatch.

Files: independent_candidate_bounds.py is the checker; independent_candidate_bounds_result.json contains all exact interval and symbolic-pair data; independent_candidate_bounds.log records execution; independent_candidate_bounds_completion.json records process exit and hashes. All new files use separate names; frozen tree and previous pair checker artifacts are untouched. This package supports the candidate-parameter portion of a proof; it is not a complete formal nine-point theorem. No Lean installation is performed.
