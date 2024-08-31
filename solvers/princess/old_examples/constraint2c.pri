/**
 * The linear unification constraint
 *   f(f(X)) = f(f(Y)+1+Z)    (Z >= 0)
 */


\predicates {
        f(int, int);
}

\problem {
// Totality
//	\forall int x; \exists int y; f(x, y)
//->
// Functionality
        \forall int x, y1, y2; (f(x, y1) -> f(x, y2) -> y1 = y2)
->

(
	\exists int y; \forall int x; f(x, y)
|
	\exists int x, y, fx, fy; (f(x,fx) & f(y,fy) & fx != fy)
)
->
        \exists int x, y, z; (
		z >= 0 &
        \forall int fx, fy, ffx, ffyz; (
                f(x, fx)
        ->
                f(y, fy)
        ->
                f(fx, ffx)
        ->
                f(fy+1+z, ffyz)
        ->
                ffx = ffyz
        )
        )
}