
Set Implicit Arguments.

Module Fun.

Definition f {X} (h:nat->X)(g:X->nat) := g (h 0).

Definition f_set := f S S.
Definition f_prop := f (fun _ => I) (fun _ => 1).
Definition f_type := f (fun _ => nat) (fun _ => 1).

End Fun.

Recursive Extraction Fun.


Module Ind.

Inductive t (X:Type) : Type := T : (nat->X)->(X->nat)-> t X.

Definition f {X} (x : t X) := match x with T h g => g (h 0) end.

Definition f_set := f (T S S).
Definition f_prop := f (T (fun _ => I) (fun _ => 1)).
Definition f_type := f (T (fun _ => nat) (fun _ => 1)).

End Ind.

Recursive Extraction Ind.


Module Match.

Definition t (b:bool) := if b then nat else True.

Definition f (b:bool)(h:nat->t b)(g:t b ->nat) := g (h 0).

Definition f_true := f true S S.
Definition f_false := f false (fun _ => I) (fun _ => 1).

End Match.

Recursive Extraction Match.


Module Poly.

Definition f {X} (p : (nat -> X) * True) : X * nat :=
  (fst p 0, 0).

Definition f_set := f (S,I).
Definition f_prop := f ((fun _ => I),I).
Definition f_type := f ((fun _ => nat),I).

End Poly.

Recursive Extraction Poly.

(* !! le polyprop warning est H.S. en 8.5 !! *)


Module Fix.

Fixpoint arity (X:Type) n : Type := match n with
 | 0 => nat
 | S n => (nat->X)->arity X n
end.

Fixpoint f {X} n (g:X->nat) acc : arity X n := match n with
 | 0 => acc
 | S n => fun (h:nat->X) => f n g (g (h acc))
end.

Definition f_nat := f 2 S 0 S S.
Definition f_prop := f 2 (fun _=>3) 0 (fun _=>I) (fun _=>I).

End Fix.

Recursive Extraction Fix.
