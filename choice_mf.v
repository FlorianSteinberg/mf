From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop mf_tight.
Import Morphisms.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section choice_mf.
Context (S T: Type).
Lemma exists_choice (f: S ->> T) (t: T):
	exists F, F \is_choice_for f.
Proof.
set R := make_mf (fun s t => forall t', f s t' -> f s t).
have [s | F tot]:= choice (mf.value R); last by exists F => s; apply /tot.
case: (classic (s \from dom f)) => [[] t' fst | false]; first by exists t'.
by exists t => t' fst'; exfalso; apply false; exists t'.
Qed.

Lemma F2MF_sing_tot (f: S ->> T) (t: T):
	f \is_singlevalued /\ f \is_total <-> exists g, (F2MF g) =~= f.
Proof.
split => [ [sing tot] | [g eq] ].
	have [g icf]:= exists_choice f t.
	exists g; by apply/ sing_tot_F2MF_icf.
by split; rewrite -eq; [apply F2MF_sing | apply F2MF_tot].
Qed.

Lemma icf_tight (g f: S ->> T): (forall s, exists t', ~ f s t')
	-> (forall h, (h \is_choice_for g -> h \is_choice_for f)) -> (g \tightens f).
Proof.
rewrite !tight_char.
move => ex prop s [t fst].
split => [ | t' gst'].
	have [t' nfst']:= (ex s).
	pose g' := make_mf (fun x y => (x <> s -> g x y) /\ (x = s -> y = t')).
	have [h icf'] := (exists_choice g' t).
	apply NNPP => nex.
	have ngst': ~g s t' by move => gst'; apply nex; exists t'.
	have icf: h \is_choice_for g.
		move => s' t'' gs't''.
		case (classic (s' = s)) => [eq | neq].
			by exfalso; apply nex; exists t''; rewrite -eq.
		have g's't'': g' s' t'' by split => // eq; exfalso; apply neq.
		exact: ((icf' s' t'' g's't'').1 neq).
	suffices eq: h s = t' by apply nfst'; rewrite -eq; apply: (prop h icf s t).
	have g'st': g' s t' by trivial.
	by apply (icf' s t' g'st').2.
pose g' := make_mf (fun x y => g x y /\ (x = s -> y = t')).
have gtg: g' \tightens g.
	rewrite !tight_char.
	move => x xfd.
	split => [ | y g'xy]; last by apply g'xy.1.
	case (classic (x = s)) => [ eq | neq ]; first by exists t'; rewrite eq.
	by have [y gxy]:= xfd; exists y; by split.
have [h icf']:= (exists_choice g' t).
have icf: h \is_choice_for g.
	apply icf_F2MF_tight.
	apply/ tight_trans; first by apply/ gtg.
	by apply icf_F2MF_tight; apply icf'.
suffices val: h s = t' by rewrite -val; apply/ (prop h icf s t).
have val': g s t' /\ (s = s -> t' = t') by split.
by apply: (icf' s t' val').2.
Qed.
End choice_mf.
