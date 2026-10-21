# Frozen mathematical statement: Thomson N=9, Coulomb energy

Version 1. This is a specification, not a proof.

Ambient space: Euclidean R^3. Admissible configurations: nine pairwise distinct vectors of norm one. Energy: sum over 1 <= i < j <= 9 of 1 / EuclideanDistance(x_i,x_j), each unordered pair exactly once. No symmetry, stationarity or separation hypothesis restricts competitors in the final theorem.

For 0<r<1 let h=sqrt(1-r^2). The candidate consists of (r cos(2 pi k/3),r sin(2 pi k/3),+/-h) and (cos((2k+1)pi/3),sin((2k+1)pi/3),0), k=0,1,2.

Define E_D(r)=sqrt(3)+2sqrt(3)/r+3/(2sqrt(1-r^2))+6/sqrt(4-r^2)+12/sqrt(2-r)+6/sqrt(2+2r). The parameter r_* must be proved to exist and to be the unique stationary point in (0,1). A finite decimal or interval midpoint is not the exact parameter.

Final target: for every admissible X, E(X)>=E_D(r_*), and the stated candidate is admissible and attains E_D(r_*). This target is unconditional once all its lemmas are proved. Global uniqueness up to O(3) and permutations is excluded from this version.

Required semantic checks: real dimension 3; radius 1; mutual distinctness (Lean inverse 0=0 must not admit collisions); unsquared distance inverse, not inverse-square distance; correct pair counting; all arbitrary competitors; existence and uniqueness of r_*; exact candidate energy; no new certificate-validity axiom.

The present independent tree checker, when implemented, will initially establish only conditional residual nonnegativity given coefficient enclosures and valid local regions. This is an explicit intermediate theorem, not the final N=9 claim.
