.PHONY: espresso release build test check all clean gradualize check_ast_trans_ty \
	check_syntax_antidote check_ast_trans_antidote check_types_antidote \
	check_syntax_riak check_ast_trans_riak check_types_riak

REBAR = rebar3

all: build check test

espresso:
	cd c_src/espresso && make

release: espresso
	$(REBAR) as prod escriptize
	cp _build/espresso _build/prod/bin/espresso

build: espresso
	$(REBAR) escriptize
	cp _build/espresso _build/default/bin/espresso

clean:
	$(REBAR) clean
	rm -rf _build _etylizer rebar.lock

test: build testtest
	@echo "Running unit tests for type checker ..."
	$(REBAR) eunit
	@echo "Checking syntax transformation for source code of type checker ..."
	./_build/default/bin/etylizer --sanity --no-type-checking -I ./src ./src/*.erl
	@echo "Running case study ..."
	ETYLIZER_CASE_STUDY_LOGLEVEL=warn test_files/etylizer-mini/check-orddict.sh
	ETYLIZER_CASE_STUDY_LOGLEVEL=warn test_files/etylizer-mini/check-std.sh
	ETYLIZER_CASE_STUDY_LOGLEVEL=warn test_files/etylizer-mini/check.sh
	@echo "Running property-based tests ..."
	$(REBAR) proper

testtest:
	@echo "Running unit tests for tests ..."
	$(REBAR) eunit -d test_files/tycheck/
	$(REBAR) eunit -d test_files/tycheck_disabled/

check:
	$(REBAR) as test dialyzer

gradualize:
	cd src && gradualizer --fmt_location brief *.erl

check_ast_trans_etylizer: build
	./etylizer --sanity -I ./src ./src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_etylizer: build
	./etylizer --no-type-checking ./src/*.erl

# Checked with commit c6e6acc290487251b419578d2ed7c65167b033ad
check_syntax_antidote: build
	./etylizer -I ~/repos/antidote/include/ -I ~/repos -c src/ast_erl.erl ~/repos/antidote/src/*.erl

# Checked with commit b6ce46f2753d0b3131beb014fa9c92c3bb1ab74b
check_ast_trans_antidote: build
	./etylizer --sanity -I ~/repos/antidote/include/ -I ~/repos ~/repos/antidote/src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_antidote: build
	cd ~/devel/antidote && ~/devel/etylizer/etylizer --no-type-checking -S src/ -I include/ -I ~/devel/

# Checked with commit 1f7e204548148f7dda9727113838d40b559310e3
# ~/repos/riak_core must contain riak_core_stat_xform.beam
check_syntax_riak: build
	./etylizer --pa ~/repos/riak_core/ --level error -D namespaced_types -I ~/repos/riak_core/include/ -c src/ast_erl.erl ~/repos/riak_core/src/*.erl

# Checked with commit a6994aff8f72b31ed3bd20c36879968ca8362fa1
# ~/repos/riak_core must contain riak_core_stat_xform.beam
check_ast_trans_riak: build
	./etylizer --sanity --pa ~/repos/riak_core/ --level error -D namespaced_types -I ~/repos/riak_core/include/ ~/repos/riak_core/src/*.erl

# Checked with commit 9670af61618f4e05208c58101baea43e49bb9c28
check_types_riak: build
	cd ~/devel/riak_core && ~/devel/etylizer/etylizer --no-type-checking -S src/ -D namespaced_types -I include/ -I ~/devel/
