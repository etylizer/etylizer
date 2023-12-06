.PHONY: build test check all clean gradualize check_ast_trans_ty \
	check_syntax_antidote check_ast_trans_antidote check_types_antidote \
	check_syntax_riak check_ast_trans_riak check_types_riak

REBAR = ./rebar3

build:
	$(REBAR) escriptize

clean:
	$(REBAR) clean
	rm -rf _build _etylizer rebar.lock

test: build testtest
	@echo "Running unit tests for type checker ..."
	$(REBAR) eunit
	@echo "Checking syntax transformation for source code of type checker ..."
	./_build/default/bin/ety --sanity --no-type-checking -I ./src ./src/*.erl

advtest: build
	@echo "Running advanced tests for type checker ..."
	rm -rf _etylizer #TODO --force flag?
	./ety -l debug test_files/tycheck/check_if.erl -o foo -o bar
	! ./ety -l debug test_files/tycheck/check_if_fail.erl -o foo -o bar
	./ety -l debug test_files/tycheck/concat.erl
	! ./ety -l debug test_files/tycheck/concat_fail.erl
	# TODO bug
	#./ety -l debug test_files/tycheck/filtermap.erl -o my_filtermap
	! ./ety -l debug test_files/tycheck/filtermap_fail0.erl
	# TODO slow
	#! ./ety -l debug test_files/tycheck/filtermap_fail1.erl
	! ./ety -l debug test_files/tycheck/filtermap_fail2.erl
	! ./ety -l debug test_files/tycheck/filtermap_fail3.erl
	# TODO -type support
	#./ety -l debug test_files/tycheck/flatten.erl -o flatten
	#./ety -l debug test_files/tycheck/flatten.erl -o flatten_erl
	#./ety -l debug test_files/tycheck/hlist.erl -o foo -o bar
	#! ./ety -l debug test_files/tycheck/hlist_fail.erl
	# TODO funcall fail
	#! ./ety -l debug test_files/tycheck/funcall_fail.erl
	# TODO bug
	#./ety -l debug test_files/tycheck/grad-405_list.erl
	# TODO bug
	#./ety -l debug test_files/tycheck/if_refine.erl -o bar
	! ./ety -l debug test_files/tycheck/if_refine_fail1.erl -o bar
	# TODO ety:negation
	#./ety -l debug test_files/tycheck/map_even.erl
	# TODO slow
	#./ety -l debug test_files/tycheck/map_even2.erl -o my_map_infer -o even -o map_even
	#! ./ety -l debug test_files/tycheck/map_even_fail.erl -o my_map_infer -o even -o map_even
	# TODO bug
	#./ety -l debug test_files/tycheck/match.erl -o foo
	#./ety -l debug test_files/tycheck/match1.erl -o foo
	#./ety -l debug test_files/tycheck/match2.erl -o foo
	! ./ety -l debug test_files/tycheck/match_fail.erl
	! ./ety -l debug test_files/tycheck/match_fail2.erl
	./ety -l debug test_files/tycheck/my_and.erl -o my_and_infer -o my_and2_infer
	# TODO slow
	#! ./ety -l debug test_files/tycheck/my_and_fail.erl
	./ety -l debug test_files/tycheck/overloaded_fun.erl -o foo -o bar -o egg_infer
	./ety -l debug test_files/tycheck/overloaded_fun2.erl -o foo
	# TODO bug
	#./ety -l debug test_files/tycheck/overloaded_fun3.erl -o foo
	! ./ety -l debug test_files/tycheck/overloaded_fun_fail.erl
	# TODO bug
	#./ety -l debug test_files/tycheck/paper_ifl.erl
	./ety -l debug test_files/tycheck/pattern_refine.erl -o foo -o bar
	# TODO infer
	#./ety -l debug test_files/tycheck/recursive.erl
	# TODO bug
	#./ety -l debug test_files/tycheck/save_div.erl -o save_div
	! ./ety -l debug test_files/tycheck/save_div_fail.erl
	./ety -l debug test_files/tycheck/test_inf.erl
	# TODO infer
	#./ety -l debug test_files/tycheck/test_inf2.erl
	! ./ety -l debug test_files/tycheck/test_inf_fail.erl
	# TODO slow, infinite type check loop?
	#! ./ety -l debug test_files/tycheck/test_inf_fail2.erl
	# TODO named references
	#./ety -l debug test_files/tycheck/typecase.erl -o foo_infer -o foo2_infer -o foo
	#! ./ety -l debug test_files/tycheck/typecase_fail.erl
	#./ety -l debug test_files/tycheck/union.erl -o get_value -o handle_response_infer
	./ety -l debug test_files/tycheck/union_distrib.erl
	! ./ety -l debug test_files/tycheck/union_distrib_fail.erl
	#!./ety -l debug test_files/tycheck/union_fail.erl -o get_value -o handle_response_infer
	@echo "Finished without errors"



testtest:
	@echo "Running unit tests for tests ..."
	$(REBAR) eunit -d test_files/tycheck/

check:
	$(REBAR) dialyzer

all: build check test

gradualize:
	cd src && gradualizer --fmt_location brief *.erl

check_ast_trans_ety: build
	./ety --sanity -I ./src ./src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_ety: build
	./ety --no-type-checking ./src/*.erl

# Checked with commit c6e6acc290487251b419578d2ed7c65167b033ad
check_syntax_antidote: build
	./ety -I ~/repos/antidote/include/ -I ~/repos -c src/ast_erl.erl ~/repos/antidote/src/*.erl

# Checked with commit b6ce46f2753d0b3131beb014fa9c92c3bb1ab74b
check_ast_trans_antidote: build
	./ety --sanity -I ~/repos/antidote/include/ -I ~/repos ~/repos/antidote/src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_antidote: build
	cd ~/devel/antidote && ~/devel/etylizer/ety --no-type-checking -S src/ -I include/ -I ~/devel/

# Checked with commit 1f7e204548148f7dda9727113838d40b559310e3
# ~/repos/riak_core must contain riak_core_stat_xform.beam
check_syntax_riak: build
	./ety --pa ~/repos/riak_core/ --level error -D namespaced_types -I ~/repos/riak_core/include/ -c src/ast_erl.erl ~/repos/riak_core/src/*.erl

# Checked with commit a6994aff8f72b31ed3bd20c36879968ca8362fa1
# ~/repos/riak_core must contain riak_core_stat_xform.beam
check_ast_trans_riak: build
	./ety --sanity --pa ~/repos/riak_core/ --level error -D namespaced_types -I ~/repos/riak_core/include/ ~/repos/riak_core/src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_riak: build
	cd ~/devel/riak_core && ~/devel/etylizer/ety --no-type-checking -S src/ -D namespaced_types -I include/ -I ~/devel/
