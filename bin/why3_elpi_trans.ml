open Why3
open Why3_elpi

let run_c =
	declare_external_symbol
		~name:"w3_run"
		~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let transform_query ~file build_query (t : Task.task) =
	let file = resolve_program_file file in
	let _elpi, prog = get_program ~file in
	match split_focused_goal t with
	| None -> Loc.errorm "elpi: transform interface requires a task with a goal"
	| Some (rest, goal) ->
		match run_query_with prog (fun state ->
			let depth = 0 in
			let state, rest_t, eg1 =
				(Elpi_api_compat.BuiltInContextualData.list tdecl).embed
					~depth [] Elpi.API.RawData.no_constraints state rest
			in
			let state, goal_t, eg2 =
				focused_goal.embed ~depth [] Elpi.API.RawData.no_constraints state goal
			in
			let state, output_uvar = Elpi.API.FlexibleData.Elpi.make ~name:"Output" state in
			let output_t = Elpi.API.RawData.mkUnifVar output_uvar ~args:[] state in
			let state, query_term, eg3 = build_query ~depth state rest_t goal_t output_t in
			(state, query_term, eg1 @ eg2 @ eg3)) focused_task with
		| Some out_task -> out_task
		| None -> Loc.errorm "elpi: failure"

let register_transform ~name ~file ~entrypoint ~desc =
	let build_entrypoint ~depth:_ state rest_t goal_t output_t =
		let query_term =
			Elpi.API.RawData.mkAppGlobalL entrypoint [rest_t; goal_t; output_t]
		in
		(state, query_term, [])
	in
	let trans = Trans.store (transform_query ~file build_entrypoint) in
  (* Or maybe: use Args_wrapper with Ttrans_l in an attempt to unify with the other registration function?
     But that didn't work *)
	Trans.register_transform_l ~desc name trans

let register_transform_with_arg ~name ~file ~entrypoint ~embed ~arg_type ~desc =
	let make_trans arg =
		Trans.store (transform_query ~file (fun ~depth state rest_t goal_t output_t ->
			let state, arg_t, eg1 =
				embed ~depth [] Elpi.API.RawData.no_constraints state arg in
			let query_term =
				Elpi.API.RawData.mkAppGlobalL entrypoint [arg_t; rest_t; goal_t; output_t] in
			(state, query_term, eg1)))
	in
	Args_wrapper.wrap_and_register ~desc name arg_type make_trans
