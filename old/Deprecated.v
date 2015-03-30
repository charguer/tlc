




(* From LibInt *)

Axiom div_2_parts : forall n n1 n2,
  n >= 4 -> n1 = Zdiv n 2 -> n2 = n - n1 ->
  2 <= n1 /\ n1 < n /\ 2 <= n2 /\ n2 < n.

Axiom abs_ge : forall (a:int) (b:nat),
  (a >= b) -> (abs a >= b).
  
Axiom abs_gt : forall (a:int) (b:nat),
  (a > b) -> (abs a > b).



