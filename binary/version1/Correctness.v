(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(***************************************************************************)
(*                  MUTUAL EXCLUSION OF TWO PROCESSES                      *)
(*                        (Peterson's algorithm)                           *)
(*                                                                         *)
(*                             Eduardo Gimenez                             *)
(*                                (17/03/97)                               *)
(*                                                                         *)
(***************************************************************************)
(*   Proof of correctness : both processes will never be in the critic     *)
(*   section at once.                                                      *) 
(***************************************************************************)


Require Import Streams.
Require Import Def.

Definition exclusion (m : Memo) :=
  match pc m true, pc m false with
  | SC, SC => False
  | _, _ => True
  end.

Definition Correctness (m : Memo) :=
  forall o : Oracle,
  ForAll (fun x : Trace => exclusion (hd x)) (protocol m o).

Theorem correct : Correctness initial.
Proof.


(************************************************************************
  The --infinite!-- proof consists in constructing the automaton of
  transitions form the initial state, verifying for each one that
   the property of exclusion is satisfied. The proof for each node
   follows the same scheme : 
     (1) inspect the first boolean of the oracle,
     (2) apply the constructor forall,
     (3) the proof of exclusion for the current state of the memory 
         follows trivially by definition,
     (4) keep the proof for each of the two child nodes 
         (the wright childs are automatically 
          looked up into the context by Auto).
  This pattern is defined by the following tactical :
**************************************************************************)


Ltac Connect :=
  unfold Correctness in |- *; intro o; case o; intro b; case b;
   (intros; constructor; [ exact I | simpl in |- *; auto ]).



(***************************************************************************
  Since the proof for each node depends on the other ones, they have
  to be proven all together, in a mutually dependent guarded
  declaration.
 ****************************************************************************)

(* We introduce the different states of the automaton ... *)

Notation st := (proc true initial) (only parsing).
Notation stt := (proc true (proc true initial)) (only parsing).
Notation stf := (proc false (proc true initial)) (only parsing).
Notation sttf := (proc false (proc true (proc true initial))) (only parsing).
Notation sf := (proc false initial) (only parsing).
Notation sft := (proc true (proc false initial)) (only parsing).
Notation sff := (proc false (proc false initial)) (only parsing).
Notation sfft := (proc true (proc false (proc false initial))) (only parsing).
Notation sfff := (proc false (proc false (proc false initial)))
  (only parsing).

(* ... and we connect them *)

cofix correct_initial with (correct_st : Correctness (proc true initial))
 (correct_stt : Correctness (proc true (proc true initial)))
 (correct_stf : Correctness (proc false (proc true initial)))
 (correct_sttf : Correctness (proc false (proc true (proc true initial))))
 (correct_sf : Correctness (proc false initial))
 (correct_sft : Correctness (proc true (proc false initial)))
 (correct_sff : Correctness (proc false (proc false initial)))
 (correct_sfft : Correctness (proc true (proc false (proc false initial))))
 (correct_sfff : Correctness (proc false (proc false (proc false initial))));
 Connect.
Qed.
