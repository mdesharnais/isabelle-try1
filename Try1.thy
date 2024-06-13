theory Try1
  imports Pure
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

local

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss;

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
      "Trying " ^ space_implode " " (serial_commas "and" (map quote proof_methods)) ^ "..."
      |> writeln
    else
      ();
    get_results proof_methods
  end;

in

fun generic_try1 mode (timeout_opt : Time.time option) (facts_override : facts_override)
  (st : Proof.state) =
  let
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

end
\<close>


end
