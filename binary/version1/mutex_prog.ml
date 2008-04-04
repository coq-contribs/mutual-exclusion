open Mutex
open Tk

(* Pierre Letouzey - 07 March 04 *)

(* A small graphical interface for visualizing the Petersson algorithm.
   Based on the original interface in Haskell+Fudgets by E. Gimenez,
   Except that we use here the [protocol] function (from stream to stream)
   instead of the simplier [proc] (from state to next state).
   There's more fun this way ... 
*)


(* printing function *)
let bool2str = function True -> "true" | False -> "false"
let etat2str = function OUT -> "OUT" | DEM -> "DEM" | SC -> "SC "
let memo2str {pc1=m1; pc2=m2; tour=b} = 
  "<"^(etat2str m1)^","^(etat2str m2)^","^(bool2str b)^">"

(* Tk widgets *)
let top = openTk ()
let left = Button.create top ~width:10 ~text:"Launch left" 
let right = Button.create top ~width:10 ~text:"Launch right"
let out = Label.create top ~width:15 ~relief:`Sunken

(* A reference containing the last action of the user. *)
let which = ref True

(* A stream that will contains all successive actions of the user. *)
let rec build_oracle () = lazy (Cons (!which, build_oracle ()))

(* The output stream build by the [protocol2] extracted function.  *)
let str = ref (protocol2 initial (build_oracle ())) 

(* [update] refreshes the display and shifts [str] to its tail. *)
let update () = 
  let Cons (m,s) = Lazy.force !str in 
  Label.configure out ~text:(memo2str m); str:=s

let _ = 
  pack [coe out;coe left;coe right]; 
  Button.configure left ~command:(fun () -> which := True; update ());
  Button.configure right ~command:(fun () -> which := False; update ());
  (* Initial display = the value of [initial]. 
     No call to [build_oracle] yet, thanks to the lazy/force hack in [Mutex] *)
  update (); 
  mainLoop ()
