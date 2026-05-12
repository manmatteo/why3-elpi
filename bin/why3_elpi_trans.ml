let run_c =
	Why3_elpi.declare_external_symbol
		~name:"w3_run"
		~ty:"list tdecl -> focused-goal -> list focused-task -> prop"

let transform_query ~file build_query (t : Why3.Task.task) =
	let open Why3_elpi in
	let _elpi, prog = Why3_elpi.get_program ~file in
	match Why3_elpi.split_focused_goal t with
	| None -> Why3.Loc.errorm "elpi: transform interface requires a task with a goal"
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
		| None -> Why3.Loc.errorm "elpi: failure"

let register_transform ~name ~file ~entrypoint ~desc =
	let build_query ~depth:_ state rest_t goal_t output_t =
		let query_term =
			Elpi.API.RawData.mkAppGlobalL entrypoint [rest_t; goal_t; output_t]
		in
		(state, query_term, [])
	in
	let trans = Why3.Trans.store (transform_query ~file build_query) in
	Why3.Trans.register_transform_l ~desc name trans

let build_transform_with_embedded_args ~file ~entrypoint embeds =
	let build_query ~depth state rest_t goal_t output_t =
		let state, args_t, egs =
			List.fold_left
				(fun (state, args_t, egs) embed ->
					let state, arg_t, eg = embed ~depth state in
					(state, arg_t :: args_t, egs @ eg))
				(state, [], []) embeds
		in
		let query_term =
			Elpi.API.RawData.mkAppGlobalL entrypoint
				(List.rev_append args_t [rest_t; goal_t; output_t])
		in
		(state, query_term, egs)
	in
	Why3.Trans.store (transform_query ~file build_query)

let register_transform_with_args ~name ~arg_type ~desc make_trans =
	Why3.Args_wrapper.wrap_and_register ~desc name arg_type make_trans