# Independent H27 and R_H construction

The completed result is INDEPENDENT_H27_RH_BINDING_PASS. All 28 independently constructed H power-coefficient enclosures are contained in the corresponding original coefficient-model boxes. All 807 independently assembled R_H coefficient enclosures are also contained in the original boxes. Both exponent supports agree exactly. This is containment, not interval overlap.

independent_hermite_RH.py imports only independent_integer_interval.py, whose 640-bit signed-integer interval operations were compared endpoint-for-endpoint with the independent Fraction-backed implementation over 5,984 test cases. It imports no archived Hermite, export, coefficient or interval helper. contact_minorant_factor_v1.py was read solely to identify the mathematical node specification: the six candidate inner products and the eight supplementary rationals -1, -9/10, -2/5, -1/5, 1/10, 9/20, 13/25, 14/25. The six algebraic nodes use the independently refined stationary-root bracket from the preceding N/contact construction. That bracket is nested in the original radius interval and has width at most 2^-500.

The 14 distinct node intervals are sorted and required to be disjoint, ordered, inside [-1,1), with the endpoint 1 excluded. Each exact node appears twice in the confluent list. For the triangular divided-difference table T[i,j], T[i,0]=f(z_i). At the repeated adjacent pair and order j=1, T[i,1]=fprime(z_i) directly. Every other entry uses (T[i,j-1]-T[i-1,j-1])/(z_i-z_(i-j)). There are 364 such divisors, all proved strictly positive by interval endpoints. f(t)=1/sqrt(2-2t) and fprime(t)=f(t)/(2-2t) are independently evaluated. No subtraction of nearly equal repeated nodes is permitted.

The Newton coefficients are the diagonal T[j,j]. They are converted to the ascending power basis by the nested multiplication H_j(t)=a_j+(t-z_j)*H_(j+1)(t). The result saves the full triangular table, all diagonal coefficients, all repeated and distinct nodes, every strict divisor enclosure, and all 28 power coefficients. In exact real arithmetic the confluent interpolation theorem gives the unique degree-at-most-27 polynomial satisfying H(node)=f(node), Hprime(node)=fprime(node). The interval computation encloses that exact construction. Zero-containing evaluation residuals are not used as proof of these equalities.

For every t in [-1,1), the ordinary confluent Hermite remainder theorem gives

f(t)-H(t) = f^(28)(xi)/28! * product_(14 distinct nodes a) (t-a)^2,

where xi lies in the interval containing t and all the nodes. Direct differentiation gives f^(28)(xi)=55!!*(2-2*xi)^(-57/2)>0 because xi<1. The product of squares is nonnegative, hence H(t)<=f(t). At an interpolation node equality already holds by the interpolation theorem. These are explicitly stated real-calculus lemmas, not Lean formalizations and not deductions from interval zero containment. No uniform remainder magnitude or Stieltjes K-factor bound is asserted by this task.

The R_H assembly consumes the completed independent F/c binding. With its actual new F and c, it constructs

R_H(u,v,t)=H(u)+H(v)+H(t)-7F(u,v,t)-F(1,u,u)-F(1,v,v)-F(1,t,t)-c.

Each diagonal substitution is performed on the full three-variable F coefficient map: the first exponent is discarded and the second plus third exponent becomes the remaining univariate degree. Every R_H coefficient is then compared with the corresponding original R coefficient interval using exact rational endpoint inequalities. The full new sparse map is saved, suitable as input to a subsequent independent local verifier. This does not independently establish R_H nonnegativity.

independent_hermite_component_tests.json records an independent interpolation test using p(t)=t^27+3t^2-7t+5 and its exact derivative at 14 rational nodes; all 28 recovered coefficient enclosures contain the known exact coefficients. Four mathematical negative cases are rejected: duplicate nodes, reversed ordering, 13 nodes and a node at the pole t=1. The main construction and this test process both exited 0. The main construction took 3.4631046869326383 seconds.

The construction completion manifest records SHA256 hashes of code, full results, logs, test result, documentation, input node specification and all source artifacts. It verifies that the previous N/contact/F/c files remain unchanged. All output files were created under new names with exclusive creation; earlier artifacts and certificates were not modified.

This layer establishes an independently built contact minorant and R_H coefficient containment. Exact satisfaction of the unselected 12 contact equations still requires the independent rank33/W compatibility check. The 12 local certificates and main-tree leaf witnesses remain separate obligations. No full nine-point proof or Lean installation is part of this task.
