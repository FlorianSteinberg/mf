From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_tot mf_sing mf_tight mf_prod.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sums.
Context (S T S' T': Type).
(* A modification of the following construction is used to define the sum of represented spaces. *)
Definition mf_fsum S T S' T' (f : S ->> T) (g : S' ->> T') :=
  make_mf (fun c x => match c with
    | inl a => match x with
      | inl y => f a y
      | inr z => False
    end
    | inr b => match x with
      | inl y => False
      | inr z => g b z
    end
  end).
Notation "f +s+ g" := (mf_fsum f g) (at level 50).

Definition	 fsum S T S' T' (f: S -> T) (g: S' -> T') :=
	fun ss' => match ss' with
		| inl s => inl (f s)
		| inr s' => inr (g s')
	end.
Notation "f +s+_f g" := (fsum f g) (at level 50).

Lemma	F2MF_fsum (f: S -> T) (g: S' -> T'):
	F2MF (f +s+_f g) =~= (F2MF f) +s+ (F2MF g).
Proof.
split; rewrite /F2MF; first by move <-; case s => /=.
by case: s => /=; case: s0 => //= s t ->.
Qed.

Lemma fsum_sing (f: S ->> T) (g: S' ->> T'):
	f \is_singlevalued -> g \is_singlevalued -> (f +s+ g) \is_singlevalued.
Proof.
move => fsing gsing [s [t [r /=fst fsr | r'] | t' [r | r']]| s' [t [r | r'] | t' [r | r' /= gs't' gs'r']]] //.
	by rewrite (fsing s t r).
by rewrite (gsing s' t' r').
Qed.

End sums.
Notation "f '+s+' g" := (mf_fsum f g) (at level 50).
Notation "f '+s+_f' g" := (fsum f g) (at level 50).