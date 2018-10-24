From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop.
Require Import Classical.

Section classical_mf.
Context (S T: Type).

Lemma mono_tot (f: S ->> T): f \is_mono -> f \is_total.
Proof.
move => inj s.
apply not_all_not_ex => all.
pose g := F2MF (fun (b: bool) => s).
pose h := @empty_mf bool S.
suff eq: g =~= h by have /=<-:= eq true s.
apply inj.
rewrite comp_F2MF comp_empty_r => q r /=.
by split => // fsr; apply (all r).
Qed.

Lemma sing_tot_mono (f: S ->> T): (f\^-1) \is_singlevalued -> f \is_total -> f \is_mono.
Proof.
move => sing tot R g h eq r s.
have [t fst]:= tot s.
have eq':= eq r t.
case: (classic (f o g r t)) => [cmp | ncmp].
	have: g r s.
		have [[s' [grs' fs't]] _]:= cmp.
		by rewrite (sing t s s').
	suff: h r s => //.
	move: cmp; rewrite eq'; move => [[s' [grs' fs't]] _].
	by rewrite (sing t s s').
have ngrs: ~ g r s by move => grs; apply/ncmp/comp_rcmp => //; exists s.
suff nhrs: ~ h r s => //.
by move => hrs; apply /ncmp; rewrite eq'; apply /comp_rcmp => //; exists s.
Qed.

Lemma sur_cotot (f: S ->> T): f \is_epi -> f \is_cototal.
Proof.
move => fsur t.
pose g := make_mf (fun t' b => t = t' /\ b = true).
pose h := make_mf (fun t' b => t = t' /\ b = false).
apply NNPP => notcodom.
have eq: g =~= h.
	apply (fsur bool g h) => s b.
	split => [] [[t' [val1 val2]] prop];
	by exfalso; apply notcodom; exists s; rewrite val2.1.
case: (classic (g t true)) => ass; last by apply ass.
by case: ((eq t true).1 ass).
Qed.

Lemma sing_cotot_sur (f: S ->> T):
f \is_singlevalued -> (f \is_cototal <-> f \is_epi).
Proof.
split => [fcotot Q g h eq t q| ]; last exact: sur_cotot.
split => ass; move: (fcotot t) => [] s fst.
	suffices gfsq: (g o f) s q.
		by move: ((eq s q).1 gfsq) => [] [] t' [] fst'; rewrite (H s t t').
	by split => [ | t' fst']; [exists t | exists q; rewrite (H s t' t)].
have hfsq: (h o f) s q.
	by split => [ | t' fst']; [ exists t| exists q; rewrite (H s t' t) ].
by move: ((eq s q).2 hfsq) => [] [] t' [] fst'; rewrite (H s t t').
Qed.

Lemma sur_fun_sur (f: S -> T):
	f \is_surjective_function <-> (F2MF f) \is_epi.
Proof.
split => sur.
	move => R g h.
	rewrite !comp_F2MF => eq s t.
	have [r <-]:= sur s.
	exact: (eq r t).
move => t.
have cotot: (F2MF f) \is_cototal by apply sur_cotot.
have [s fst]:= cotot t.
by exists s.
Qed.
End classical_mf.
