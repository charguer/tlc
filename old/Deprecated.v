-----

Class BagRead A B T := { read : T -> A -> B }.
Class BagUpdate A B T := { update : T -> A -> B -> T }.




Instance read_inst : BagRead nat nat nat.
Admitted.

Instance update_inst : BagUpdate nat nat nat.
Admitted.


Lemma test : forall m x : nat,
  m [ x := 3 ][ x := 3 ][3][5][ x := 3 ] = 0.


------



(* From LibInt *)

Axiom div_2_parts : forall n n1 n2,
  n >= 4 -> n1 = Zdiv n 2 -> n2 = n - n1 ->
  2 <= n1 /\ n1 < n /\ 2 <= n2 /\ n2 < n.

Axiom abs_ge : forall (a:int) (b:nat),
  (a >= b) -> (abs a >= b).
  
Axiom abs_gt : forall (a:int) (b:nat),
  (a > b) -> (abs a > b).



