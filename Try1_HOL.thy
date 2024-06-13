theory Try1_HOL
  imports Try1 Main
begin

ML \<open>
local

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods (debug : bool) : Proof.context -> Proof.context =
  Config.put Metis_Tactic.verbose debug
  #> not debug ? (fn ctxt =>
      ctxt
      |> Simplifier_Trace.disable
      |> Context_Position.set_visible false
      |> Config.put Unify.unify_trace false
      |> Config.put Argo_Tactic.trace "none"
      |> Proof_Context.background_theory (fn thy =>
          thy
          |> Context_Position.set_visible_global false
          |> Config.put_global Unify.unify_trace false));

fun can_apply timeout_opt pre post tac st =
  let val {goal, ...} = Proof.goal st in
    (case (case timeout_opt of
            SOME timeout => Timeout.apply_physical timeout
          | NONE => fn f => fn x => f x) (Seq.pull o tac) (pre st) of
      SOME (x, _) => Thm.nprems_of (post x) < Thm.nprems_of goal
    | NONE => false)
  end;

fun apply_generic timeout_opt command pre post apply st =
  if try (can_apply timeout_opt pre post apply) st = SOME true then
    SOME command
  else
    NONE;

fun parse_method keywords s =
  enclose "(" ")" s
  |> Token.explode keywords Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source");

fun apply_named_method_on_first_goal ctxt =
  parse_method (Thy_Header.get_keywords' ctxt)
  #> Method.method_cmd ctxt
  #> Method.Basic
  #> (fn m => Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [m]))
  #> Proof.refine;

fun add_attr_text (NONE, _) s = s
  | add_attr_text (_, []) s = s
  | add_attr_text (SOME x, fs) s =
    s ^ " " ^ (if x = "" then "" else x ^ ": ") ^ space_implode " " fs;

fun attrs_text (sx, ix, ex, dx)
    ({simp_add = ss, intro_add = is, elim_add = es, dest_add = ds} : Try1.facts_override) =
  "" |> fold add_attr_text [(sx, ss), (ix, is), (ex, es), (dx, ds)];

fun apply_named_method (name, ((all_goals, run_if_auto_try), attrs)) mode timeout_opt
    (facts_override : Try1.facts_override) st =
  let val st = Proof.map_contexts (silence_methods false) st in
    if mode <> Try1.Auto_Try orelse run_if_auto_try then
      let val attrs = attrs_text attrs facts_override in
        apply_generic timeout_opt
          ((name ^ attrs |> attrs <> "" ? enclose "(" ")") ^
           (if all_goals andalso Thm.nprems_of (#goal (Proof.goal st)) > 1 then "[1]" else ""))
          I (#goal o Proof.goal)
          (apply_named_method_on_first_goal (Proof.context_of st) (name ^ attrs)
            #> Seq.filter_results) st
      end
    else
      NONE
  end

val full_attrs = (SOME "simp", SOME "intro", SOME "elim", SOME "dest");
val clas_attrs = (NONE, SOME "intro", SOME "elim", SOME "dest");
val simp_attrs = (SOME "add", NONE, NONE, NONE);
val metis_attrs = (SOME "", SOME "", SOME "", SOME "");
val no_attrs = (NONE, NONE, NONE, NONE);

(* name * ((all_goals, run_if_auto_try), (simp, intro, elim, dest) *)
val named_methods =
  [("simp", ((false, true), simp_attrs)),
   ("auto", ((true, true), full_attrs)),
   ("blast", ((false, true), clas_attrs)),
   ("metis", ((false, true), metis_attrs)),
   ("argo", ((false, true), no_attrs)),
   ("linarith", ((false, true), no_attrs)),
   ("presburger", ((false, true), no_attrs)),
   ("algebra", ((false, true), no_attrs)),
   ("fast", ((false, false), clas_attrs)),
   ("fastforce", ((false, false), full_attrs)),
   ("force", ((false, false), full_attrs)),
   ("meson", ((false, false), metis_attrs)),
   ("satx", ((false, false), no_attrs)),
   ("order", ((false, true), no_attrs))];

in

val () = List.app (fn (pair as (name, _)) =>
  Try1.register_proof_method name (apply_named_method pair)
  handle Symtab.DUP _ => ()) named_methods

end
\<close>

declare [[try1_schedule = "order presburger linarith algebra | argo metis | simp auto blast fast fastforce force meson satx"]]

end