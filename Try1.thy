theory Try1
  imports Main
  keywords "try1" :: diag
begin

ML \<open>
signature TRY1 =
sig
  val schedule : string Config.T

  type facts_override =
    {simp_add : string list,
     intro_add : string list,
     elim_add : string list,
     dest_add : string list}

  datatype mode = Auto_Try | Try | Normal;

  type proof_method =
    mode -> Time.time option -> facts_override -> Proof.state -> string option

  val register_proof_method : string -> proof_method -> unit
  val get_all_proof_methods : unit -> (string * proof_method) list
  val get_all_proof_method_names : unit -> string list

  val try1 : Time.time option -> facts_override -> Proof.state -> (string * string * int) list
end;

structure Try1 : TRY1 =
struct

val schedule = Attrib.setup_config_string \<^binding>\<open>try1_schedule\<close> (K "")

type facts_override =
  {simp_add : string list,
   intro_add : string list,
   elim_add : string list,
   dest_add : string list}

val empty_facts_override = {simp_add = [], intro_add = [], elim_add = [], dest_add = []}

fun facts_override_of_quad (simp_add, intro_add, elim_add, dest_add) =
  {simp_add = simp_add, intro_add = intro_add, elim_add = elim_add, dest_add = dest_add}

datatype mode = Auto_Try | Try | Normal;

type proof_method =
  mode -> Time.time option -> facts_override -> Proof.state -> string option

val noneN = "none";

val default_timeout = seconds 5.0;


local
  val proof_methods =
    Synchronized.var "Try0.proof_methods" (Symtab.empty : proof_method Symtab.table);
in

fun register_proof_method name proof_method =
  (if name = "" then error "Registering unnamed proof method" else ();
   Synchronized.change proof_methods (Symtab.update_new (name, proof_method)));

fun get_proof_method name = Symtab.lookup (Synchronized.value proof_methods) name;

fun get_all_proof_methods () =
  Symtab.fold (fn x => fn xs => x :: xs) (Synchronized.value proof_methods) []

fun get_all_proof_method_names () =
  Symtab.fold (fn (name, _) => fn names => name :: names) (Synchronized.value proof_methods) []

end

fun time_string ms = string_of_int ms ^ " ms";
fun tool_time_string (s, ms) = s ^ ": " ^ time_string ms;

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

local

fun generic_try1_step mode (timeout_opt : Time.time option) (facts_override : facts_override)
  (st : Proof.state) (proof_methods : string list) =
  let
    fun trd (_, _, t) = t
    fun try_method name =
      (case get_proof_method name of
        NONE => (writeln ("Ignoring unknown proof method " ^ quote name); NONE)
      | SOME method =>
        let
          val time_begin = Time.now ()
          val result = method mode timeout_opt facts_override st
          val time_end = Time.now ()
        in
          Option.map (fn command =>
            (name, command, Time.toMilliseconds (time_end - time_begin))) result
        end);
    fun get_message (_, command, ms) = "Found proof: " ^ Active.sendback_markup_command
      ((if Thm.nprems_of (#goal (Proof.goal st)) = 1 then "by" else "apply") ^ " " ^ command) ^
      " (" ^ time_string ms ^ ")";
    val print_step = Option.map (tap (writeln o get_message));
    val get_results =
      if mode = Normal
      then Par_List.map (try_method #> print_step) #> map_filter I #> sort (int_ord o apply2 trd)
      else Par_List.get_some try_method #> the_list;
  in
    if mode = Normal then
      "Trying " ^ space_implode " " (Try.serial_commas "and" (map quote proof_methods)) ^ "..."
      |> writeln
    else
      ();
    get_results proof_methods
  end;

in

fun generic_try1 mode (timeout_opt : Time.time option) (facts_override : facts_override)
  (st : Proof.state) =
  let
    val st = Proof.map_contexts (silence_methods false) st
    val ctxt = Proof.context_of st
    val proof_methodss =
      Config.get ctxt schedule
      |> space_explode "|"
      |> map (filter (fn s => s <> "") o space_explode " ")
    fun iterate [] = []
      | iterate (step :: steps) =
        (case generic_try1_step mode timeout_opt facts_override st step of
          [] => iterate steps
        | successes=> successes)
  in
    iterate (if proof_methodss = [] then [get_all_proof_method_names ()] else proof_methodss)
  end;

end

val try1 = generic_try1 Normal

fun interpret_try1_output mode (timeout_opt : Time.time option) (facts_override : facts_override)
  (st : Proof.state) =
  (case generic_try1 mode timeout_opt facts_override st of
    [] => ((if mode = Normal then writeln "No proof found" else ()); (false, (noneN, [])))
  | xs as (name, command, _) :: _ =>
  let
    val xs = xs |> map (fn (name, _, n) => (n, name))
                |> AList.coalesce (op =)
                |> map (swap o apsnd commas);
    val message =
      (case mode of
         Auto_Try => "Auto Try0 found a proof"
       | Try => "Try0 found a proof"
       | Normal => "Try this") ^ ": " ^
      Active.sendback_markup_command
          ((if Thm.nprems_of (#goal (Proof.goal st)) = 1 then "by"
            else "apply") ^ " " ^ command) ^
      (case xs of
        [(_, ms)] => " (" ^ time_string ms ^ ")"
      | xs => "\n(" ^ space_implode "; " (map tool_time_string xs) ^ ")");
  in
    (true, (name, if mode = Auto_Try then [message] else (writeln message; [])))
  end);

fun try1_trans (facts_override : facts_override) =
  Toplevel.keep_proof
    (ignore o interpret_try1_output Normal (SOME default_timeout) facts_override o Toplevel.proof_of);

fun merge_attrs (s1, i1, e1, d1) (s2, i2, e2, d2) = (s1 @ s2, i1 @ i2, e1 @ e2, d1 @ d2);

fun string_of_xthm (xref, args) =
  Facts.string_of_ref xref ^
  implode (map (enclose "[" "]" o Pretty.unformatted_string_of o Token.pretty_src \<^context>) args);

val parse_fact_refs =
  Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) (Parse.thm >> string_of_xthm));

val parse_attr =
  Args.$$$ "simp" |-- Args.colon |-- parse_fact_refs >> (fn ss => (ss, [], [], []))
  || Args.$$$ "intro" |-- Args.colon |-- parse_fact_refs >> (fn is => ([], is, [], []))
  || Args.$$$ "elim" |-- Args.colon |-- parse_fact_refs >> (fn es => ([], [], es, []))
  || Args.$$$ "dest" |-- Args.colon |-- parse_fact_refs >> (fn ds => ([], [], [], ds));

val parse_attrs : facts_override parser =
  Args.parens (Scan.repeat parse_attr
    >> (fn quads => fold merge_attrs quads ([], [], [], []))
    >> facts_override_of_quad);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try1\<close> "try a combination of proof methods"
    (Scan.optional parse_attrs empty_facts_override #>> try1_trans);

(* val _ =
  Try.tool_setup
   {name = "try1", weight = 30, auto_option = \<^system_option>\<open>auto_methods\<close>,
    body = fn auto => generic_try1 (if auto then Auto_Try else Try) NONE empty_facts_override}; *)

end;


local

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
    NONE;

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
  Try1.register_proof_method name (apply_named_method pair)) named_methods

end
\<close>

declare [[try1_schedule = "order presburger linarith algebra | argo metis | simp auto blast fast fastforce force meson satx"]]

end
