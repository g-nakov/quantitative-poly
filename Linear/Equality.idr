module Linear.Equality

import Linear.Types

public export
replace1 : (0 p : a -> Type) -> (1 _ : x = y) -> p x -<> p y
replace1 p Refl r = r

public export
promoteEq : (0 _ : x = y) -> x = y
promoteEq Refl = Refl

public export
lcong : (f : (1 _ : t) -> u) ->
        (1 _ : a = b) -> f a = f b
lcong f Refl = Refl

public export
lcong2 : (f : (1 _ : t) -> (1 _ : s) -> u) ->
        a = b -> a' = b' -> f a a' = f b b'
lcong2 f Refl Refl = Refl

public export
lcongApp : {f, g : (1 _ : t) -> u} -> f = g -> (x : t) -> f x = g x
lcongApp Refl _ = Refl

public export
congApp : {f, g : t -> u} -> f = g -> (x : t) -> f x = g x
congApp Refl _ = Refl

public export
uip : {x, y : a} -> (p , q : x = y) -> p = q
uip Refl Refl = Refl
