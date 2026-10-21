# Nine-point Thomson: rigorous local certificate

This certificate proves strict local minimality, modulo rotations, of the stationary D3h tricapped trigonal prism. It does not prove global minimality.

## Exact centre and stationary point

Let r be the unique zero in (0,1) of

F(r)=-2sqrt(3)/r²+3r/[2(1-r²)^(3/2)]+6r/(4-r²)^(3/2)+6/(2-r)^(3/2)-6/(2+2r)^(3/2).

Existence and uniqueness follow from E''(r)>0 and divergence of E at both endpoints, where E is the standard six-distance family energy. The program rigorously brackets the zero in

[0.71054833409295381132770417927279124,
 0.71054833409295381132770417927279125].

Exact integer interval checks prove F(left)<0<F(right). Define h=sqrt(1-r²). Label points 0,1,2 as the upper triangle (angles 0,120,240 degrees), 3,4,5 as the lower triangle, and 6,7,8 as the equatorial caps (angles 60,180,300 degrees).

Why the full gradient vanishes: the horizontal and vertical mirrors through each cap force its entire tangent gradient to vanish. A vertical mirror through each prism vertex forces that vertex's tangent gradient to lie in its meridional direction. The D3h group acts transitively on the six prism vertices and carries these meridional directions into each other, using the velocity of the r-family as the reference direction. Consequently all six tangent contributions to dE/dr agree. F(r)=0 forces each of them to vanish. This uses exact symmetry and the exact root, not a small computed gradient.

## Rotation slice and chart

Fix x0. Put v1=x0-(x0·x1)x1, and let V1 be its single-column matrix. For each i=2,...,8 put vi1=xi cross ez, vi2=xi cross vi1, and Vi=[vi1 vi2]. V0 has zero columns. These bases are not normalized. They are tangent and linearly independent in the dimensions required. In particular x0·x1=1-3r²/2 is strictly between -1 and 1, so v1 is nonzero.

Use the exact normalized tangent chart

Yi(zi)=(xi+Vi zi)/sqrt(1+zi^T Gi zi),  Gi=Vi^T Vi.

There are 1+7*2=15 coordinates. The slice keeps Y0=x0 and Y1 in span(x0,x1). A nearby labeled configuration can be uniquely rotated into the relevant branch of this slice: first place its first point at x0, then use rotation about x0 to put its second point in that plane, with the nearby orientation. Thus positive definiteness in this slice proves positivity transverse to all three rotational zero modes.

## Full chart Hessian, including curvature

Set yi=xi+Vi zi, si=sqrt(1+zi^T Gi zi), wi=Gi zi. Then

Jia = via/si - yi*wia/si³,
Kiab = -(via*wib+vib*wia+yi*Giab)/si³ + 3yi*wia*wib/si⁵.

For each pair i,j, d=Yi-Yj, q=|d|, A=3dd^T/q⁵-I/q³. Its contribution to the chart Hessian is Jd^T A Jd plus the second derivative correction (-d/q³)·Kd. The code sums these contributions for all 36 pairs. It therefore certifies the actual coordinate Hessian throughout a box; it does not merely insert perturbed points into a formula valid only at stationary points.

## Outward rational intervals

Every interval endpoint is an integer divided by S=10^55. Addition is exact; multiplication takes floor of the minimum product divided by S, and ceiling of the maximum product divided by S. Reciprocals use floor(S²/upper), ceiling(S²/lower) after excluding zero. Square roots use integer isqrt(endpoint*S), increasing the upper integer unless its square is exactly the target. No floating arithmetic enters any assertion. Decimal displays are informational only.

For the symmetric 15x15 chart Hessian, exact-interval LDL elimination encloses every true pivot by induction. Successful positive lower bounds imply the exact Hessian is positive definite. The code checks the stronger statement that every pivot exceeds 1/5. This is a bound on LDL pivots, NOT a claim that every eigenvalue exceeds 1/5.

## Certified result

The point box and each box |za|<=10^-10, 10^-8, 10^-6 pass all 15 pivot inequalities. In particular throughout the explicit convex coordinate cube [-10^-6,10^-6]^15 the Hessian is positive definite. The smallest lower pivot bound is approximately 0.2758697291623636. The exact rational endpoints are in local_certificate.json and can be regenerated from the source.

Since the exact centre is stationary and the Hessian is positive definite on this convex coordinate cube, Taylor's integral formula gives E(Y(z))>E(X) for every nonzero z in the cube, and strict convexity implies no other stationary point there. Combined with the rotation slice this is a certified strict local minimum modulo rotations and an explicitly described neighborhood, not just pointwise positive definiteness.

An exploratory direct evaluation at halfwidth 10^-5 failed at pivot 15 (its enclosure straddled zero). That is failure of this interval bound, not evidence of instability.

## Reproduction and trust boundary

Run `python3 proof_work/certify_local.py` from the workspace. Only the Python standard library is needed. The certificate relies on reviewing the formulas and integer interval implementation; it has not been formalized in Lean or independently verified by another kernel. The files provide an auditable computer-assisted mathematical certificate, not a global nine-point Thomson proof.

## Stronger certificate by rational congruence preconditioning

The separate script `certify_local_preconditioned.py` proves the same strict-convexity conclusion on the 100 times wider cube [-10^-4,10^-4]^15. It constructs an exact rational unit lower triangular matrix W from rounded midpoint LDL factors at the centre, then rigorously encloses W H(z) W^T on the whole cube and runs interval LDL. W is invertible because its diagonal is exactly 1; it need not be the exact inverse of any rounded factor. Congruence therefore preserves positive definiteness exactly. All 15 preconditioned pivots are greater than 1/5, with minimum lower bound

2183981807163582174588687082401007572107889408136513962 / 10^55.

The exact W and pivot endpoint integers are stored in `local_preconditioned_certificate.json`; `python3 proof_work/certify_local_preconditioned.py --json` regenerates them. The simpler direct certificate and its narrower boxes remain independently reproducible. A 10^-3 halfwidth was not certified by this preconditioner; this is not a counterexample.
