(*Resolução da lista 5 de MFO - Polimorfismo*)
(*Aluno: Geremias Corrêa*)

(*Todas as questões resolvidas que precisem de auxiliares são importadas manualmente*)

(*A resolução da lista começa oficialmente na linha 129 deste arquivo*)

(*From LF Require Export Lists.*)

(* ################### AUXILIARES PARA A LISTA E AFINS ##########*)
(*Observação: como há problemas inexplicáveis na exportação pelo meu Ubuntu, 
eu realizo aqui imports manuais do que é necessário para realização dos exercícios*)

Module NatList.

(*Inicio Basics.v*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(*Notações, algumas por segurança, caso precise*)
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).
(*Fim Basics.v*)

(*Inicio Induction.v*)
(*Exercício 2 da aula 13/07: *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(*Lista 3 - questão 3 - disponível no arq Lista3-Q3-double_plus.v*)
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [ | n' IHn'].
  - reflexivity.  (* caso 0 = 0 * 0*)
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. (* 2 * N = N + N*)
Qed.
(*Fim Induction.v*)

(*Inicio Poly.v*)
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Definition app_list_pair {X Y : Type} (listp1 : 
  (list X) * (list Y)) (listp2 : (list X) * (list Y)) : (list X) * (list Y) :=
  (app (fst listp1) (fst listp2), app (snd listp1) (snd listp2)).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (h1, h2) :: t => app_list_pair ([h1], [h2]) (split t) 
  end.

(*Fim Poly.v*)

(*Inicio do Tatics.v*)
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.
      discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. injection eq as goal. apply goal. Qed.

(*Fim do Tatics.v*)

(* ##################  FIM DOS IMPORTS ################### *)

(*############ INÍCIO RESOLUÇÃO LISTA 5 #################*)

(*Lista 5 - questão 1:*) (*Isso?*)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x lista => f x :: lista) l nil. (*nil é elemento neutro para quanto a lista for vazia*)

(*Observações da resolução de questão 1:
(*Crio um map através do fold, sem recursão. Aqui usando fun (de função anonima) e tal*)
(*Recebe 2 argumentos: Uma função X -> Y e tbm uma lista de X, saindo uma lista dos Y mapeados*) *)
(*Obs: a função map mapeai uma função sobre uma lista, ex:
  map (fun x => x + 1) [1;2;3], na qual retorna uma lista [2;3;4]*)
(*Obs²: a função fold dobra a lista em elementos a fim de realizar uma função sobre eles, ex:
  fold fun x y => x + y) [1;2;3] 0  Na qual aqui está fazendo a soma de 1+2+3+0
*)
(*Ex: fold_map (fun x => x + 1) [1;2;3], que vira
  fold (fun x lista => (fun x => x + 1) x : lista) [1;2;3] [].
*)
  
Compute fold_map (fun x => false) [0;1;2].
(*Entra uma lista numérica x, com o mapeamento seus elementos saem bool false em uma lista Y.*)

Example test_fold_map : fold_map (mult 2) [1; 2; 3] = [2; 4; 6].
Proof. reflexivity. Qed.

(*Lista 5 - questão 2*)
Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof. 
  intros X Y f l. induction l as [ | h t IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. reflexivity.
  Qed.

(*As três abaixos são com uso do Tatics.v como apply e etc, como explicado pelo professor em sala*)

(*Lista 5 - questão 3*)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [ | n' IH].
  - intros m H. destruct m as [ | m']. (*n = 0*)
    + (*m=0*) reflexivity.
    + (*m = S m'*) discriminate. (*Isso pq é falso pois parte de premissa falsa*)
  - (*n = S n'*) intros m H. destruct m as [ | m'].
    + (*m=0*) discriminate H. (*Mesmo do discriminate anterior*)
    + (*m=S m'*) simpl in H. rewrite <- plus_n_Sm in H. 
      rewrite <- plus_n_Sm in H. injection H as H2. apply IH in H2. rewrite H2. reflexivity.
Qed. 
(*Feito com o professor em sala - 10/08 0 observações e anotações:
  A dica aqui é usar o plus_n_Sm, que afirma que S(n+m) = n + S m
  Como não consigo provar que 0 = m no caso base, precisamos usar um destruct pros 2 casos de m.
  Nesse caso, precisa dar um intro m e H só quando for destruir para não ficar com o m quantificado.
    Antes tinha um m qalquer, agora tem um específico
*)

(*LIsta 5 - questão 4*) 
Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [ | h t IH].
  - intros l1 l2 H. injection H as H1 H2. rewrite <- H1. rewrite <- H2. reflexivity. 
  - intros l1 l2. simpl. destruct h. destruct (split t). destruct l1. 
    + simpl. 
    induction l2. 
      * intros H. discriminate. 
      * discriminate. 
    + induction l2. 
      * discriminate. 
      * simpl. intros. injection H. intros. rewrite -> IH. 
        -- rewrite -> H1. rewrite -> H3. reflexivity.
        -- rewrite -> H0. rewrite -> H2. reflexivity.
Qed.

(*Lista 5 - questão 5 - Beatriz deu um help, senão não ia.*)
Theorem split_combine' : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1. generalize dependent l2.
  induction l as [| h t IHl].
  - intros l1 l2 H1 H2. destruct l1 as [| h1 t1].
    + simpl. destruct l2. reflexivity. simpl in H2. discriminate.
    + destruct l2. simpl in H1. simpl in H2. discriminate. simpl in H2. discriminate.      
  - intros  l1 l2 H H0. destruct h. simpl. destruct l2. 
      + simpl in H0. discriminate.
      + destruct l1.
        * simpl in H. discriminate. 
        * simpl in H0. injection H0. intros H1 H2 H3. simpl in H. injection H. intros. simpl. apply IHl in H4.
          -- rewrite -> H4. rewrite -> H3.  rewrite -> H2. simpl. reflexivity. 
          -- apply H1.
Qed.

(*############ FIM RESOLUÇÃO LISTA 5 #################*)