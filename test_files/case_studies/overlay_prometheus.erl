%% A spec for each of the 404 functions of the prometheus case study that have none in the source
%% (prometheus.study; prometheus_model, which gpb generates, is not part of the study and gets none).
%% The types are those of the module of the function, of the two headers and of the behaviours
%% (prometheus_metric, prometheus_collector, prometheus_format, prometheus_instrumenter, supervisor,
%% application), and what the edoc comments of the package say about the arguments.
%%
%% The types of prometheus_metric, prometheus_metric_spec and prometheus_registry that most specs
%% need are repeated below under their own names, the same definitions as in the source. A spec can
%% only name a type of a module that the calling module refers to, and the metric modules are called
%% from other applications (antidote_stats), which refer to no other module of prometheus.
%% A record of another module has no name here: the estimator of quantile_estimator.hrl is written
%% as a tuple type. The records of prometheus_model.hrl have a type each in prometheus_model.
-module(overlay_prometheus).
-compile([export_all, nowarn_export_all]).

%% prometheus_registry:registry()
-type registry() :: atom().

%% prometheus_metric:name() and prometheus_metric:help()
-type name() :: atom() | binary() | nonempty_string() | iolist().
-type help() :: binary() | string().

%% prometheus_metric:duration_unit()
-type duration_unit() :: microseconds | milliseconds | seconds | minutes | hours | days.

%% prometheus_metric_spec:spec(), a proplists:proplist(): the keys name, help, labels, registry,
%% constant_labels, duration_unit and, by metric, buckets, targets, compress_limit
-type spec() :: [atom() | tuple()].

%% The values of the labels of one series, in the order of the labels of the metric
%% (LValues :: list() in the callbacks of prometheus_metric)
-type label_values() :: [term()].

%% A label name as prometheus_metric_spec:labels/1 gives it: validate_metric_label_name/1 turns an
%% atom and a binary into a string
-type label_name() :: string().

%% prometheus_model_helpers:labels(): label names with their values, here the constant labels of a
%% metric (the pairs of the map of the spec) and the labels of a series
-type labels() :: [{term(), term()}].
-type series_labels() :: [{label_name(), term()}].

%% The row of a metric (a metric family) in the table of its metric module, as
%% prometheus_metric:insert_mf/3 writes it. Data is undefined, the buckets of a histogram or the
%% configuration of a quantile summary
-type mf() :: {{registry(), mf, name()}, {Labels :: [label_name()], help()}, CLabels :: labels(),
               duration_unit() | undefined, Data :: term()}.

%% What collect_mf/2 of a metric module gives to prometheus_model_helpers:create_mf/5, which hands it
%% to collect_metrics/2 of the module (prometheus_collector:data()): the constant labels, the names
%% of the labels and the registry; with the duration unit for a gauge and a summary; with the unit
%% and the data of the metric for a histogram and a quantile summary
-type collect_data() :: {CLabels :: labels(), [label_name()], registry()}.
-type collect_data_du() :: {CLabels :: labels(), [label_name()], registry(), duration_unit() | undefined}.
-type collect_data_du(Data) :: {CLabels :: labels(), [label_name()], registry(), duration_unit() | undefined, Data}.

%% The key of a series in the tables of prometheus_counter, prometheus_histogram, prometheus_summary
%% and prometheus_quantile_summary: one row per scheduler group (scheduler id band 15)
-type skey() :: {registry(), name(), label_values(), Scheduler :: non_neg_integer()}.

%% prometheus_buckets:bucket_bound() and buckets(), and what the key buckets of the spec of a
%% histogram can be (documented in prometheus_histogram)
-type bucket_bound() :: number() | infinity.
-type buckets() :: [bucket_bound(), ...].
-type buckets_spec() :: default | {linear, Start :: number(), Step :: number(), Count :: pos_integer()}
                      | {exponential, Start :: number(), Factor :: number(), Count :: pos_integer()}
                      | [bucket_bound()].

%% prometheus_model_helpers:prometheus_boolean(): what prometheus_boolean:set/2,3,4 takes
-type bool_value() :: boolean() | number() | list() | undefined.

%% What file:write/2 gives
-type write_ret() :: ok | {error, file:posix() | badarg | terminated}.

%% #group{} and #quantile_estimator{} of quantile_estimator.hrl, and quantile_estimator:invariant()
-type qe_group() :: {group, V :: number(), G :: number(), Delta :: number(), Rank :: number()}.
-type invariant() :: fun((number(), number()) -> number()).
-type estimator() :: {quantile_estimator, SamplesCount :: number(), DataCount :: number(),
                      InsertsSinceCompression :: non_neg_integer(), Data :: [qe_group()], invariant()}.

%% The data of a quantile summary, which prometheus_quantile_summary:validate_summary_spec/1 builds
%% from the keys targets and compress_limit of the spec: the quantiles of the targets, the invariant
%% of the estimator for them, and the number of inserts after which the estimator is compressed
-type qs_config() :: #{quantiles := [float()], invariant := invariant(), compress_limit := integer()}.

%% The type of a metric family, as prometheus_model_helpers:create_mf/4,5 take it
-type mf_type() :: gauge | counter | summary | histogram | untyped | boolean.

%% A metric of the collectors: {Name, Type, Help, Metrics} for prometheus_model_helpers:create_mf/4,
%% and the metrics that application:get_env(prometheus, COLLECTOR_metrics) enables
-type collector_metric() :: {Name :: atom(), Type :: mf_type(), help(),
                             Metrics :: prometheus_model_helpers:metrics()}.
-type enabled_metrics() :: all | [atom()].

%% ---------------------------------------------------------------------------------------------
%% prometheus
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus:start'(application:start_type(), term()) -> {ok, pid()} | {error, term()}.
'prometheus:start'(_, _) -> error(overlay).

-spec 'prometheus:stop'(term()) -> ok.
'prometheus:stop'(_) -> error(overlay).

-spec 'prometheus:start'() -> ok | {error, term()}.
'prometheus:start'() -> error(overlay).

-spec 'prometheus:stop'() -> ok | {error, term()}.
'prometheus:stop'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_buckets
%% ---------------------------------------------------------------------------------------------

%% the default buckets and infinity
-spec 'prometheus_buckets:new'() -> prometheus_buckets:buckets().
'prometheus_buckets:new'() -> error(overlay).

%% "Histogram buckets constructor". Raises no_buckets for [] and undefined, invalid_buckets for what
%% is not a list or not sorted, invalid_bound for a bound that is no number
-spec 'prometheus_buckets:new'(buckets_spec()) -> prometheus_buckets:buckets().
'prometheus_buckets:new'(_) -> error(overlay).

%% validates one element of the list of the spec
-spec 'prometheus_buckets:validate_bound'(term()) -> prometheus_buckets:bucket_bound().
'prometheus_buckets:validate_bound'(_) -> error(overlay).

%% the index, from 0, of the first bucket whose bound is not below the value
-spec 'prometheus_buckets:position'(prometheus_buckets:buckets(), Value :: number()) -> non_neg_integer().
'prometheus_buckets:position'(_, _) -> error(overlay).

-spec 'prometheus_buckets:linear'(Current :: number(), Step :: number(), Count :: non_neg_integer(),
                                  Acc :: [number()]) -> [number()].
'prometheus_buckets:linear'(_, _, _, _) -> error(overlay).

-spec 'prometheus_buckets:position'([prometheus_buckets:bucket_bound()],
                                    fun((prometheus_buckets:bucket_bound()) -> boolean()),
                                    Pos :: non_neg_integer()) -> non_neg_integer().
'prometheus_buckets:position'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_collector
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_collector:all_known_collectors'() -> [prometheus_collector:collector()].
'prometheus_collector:all_known_collectors'() -> error(overlay).

%% the collectors of the application environment; the atom default stands for the default collectors
-spec 'prometheus_collector:catch_default_collectors'([prometheus_collector:collector() | default]) ->
          [prometheus_collector:collector()].
'prometheus_collector:catch_default_collectors'(_) -> error(overlay).

-spec 'prometheus_collector:maybe_replace_default'([prometheus_collector:collector() | default],
                                                   Acc :: [prometheus_collector:collector()]) ->
          [prometheus_collector:collector()].
'prometheus_collector:maybe_replace_default'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_instrumenter
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_instrumenter:all_known_instrumenters'() -> [prometheus_instrumenter:instrumenter()].
'prometheus_instrumenter:all_known_instrumenters'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_metric
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists
-spec 'prometheus_metric:insert_new_mf'(Table :: atom(), Module :: atom(), spec()) -> ok.
'prometheus_metric:insert_new_mf'(_, _, _) -> error(overlay).

-spec 'prometheus_metric:insert_mf'(Table :: atom(), Module :: atom(), spec()) -> boolean().
'prometheus_metric:insert_mf'(_, _, _) -> error(overlay).

-spec 'prometheus_metric:deregister_mf'(Table :: atom(), registry()) -> true.
'prometheus_metric:deregister_mf'(_, _) -> error(overlay).

-spec 'prometheus_metric:deregister_mf'(Table :: atom(), registry(), name()) -> boolean().
'prometheus_metric:deregister_mf'(_, _, _) -> error(overlay).

%% raises unknown_metric and invalid_metric_arity
-spec 'prometheus_metric:check_mf_exists'(Table :: atom(), registry(), name(), label_values()) -> mf().
'prometheus_metric:check_mf_exists'(_, _, _, _) -> error(overlay).

-spec 'prometheus_metric:check_mf_exists'(Table :: atom(), registry(), name()) -> mf() | false.
'prometheus_metric:check_mf_exists'(_, _, _) -> error(overlay).

-spec 'prometheus_metric:mf_labels'(mf()) -> [label_name()].
'prometheus_metric:mf_labels'(_) -> error(overlay).

-spec 'prometheus_metric:mf_constant_labels'(mf()) -> labels().
'prometheus_metric:mf_constant_labels'(_) -> error(overlay).

-spec 'prometheus_metric:mf_duration_unit'(mf()) -> duration_unit() | undefined.
'prometheus_metric:mf_duration_unit'(_) -> error(overlay).

%% prometheus_collector:data()
-spec 'prometheus_metric:mf_data'(mf()) -> term().
'prometheus_metric:mf_data'(_) -> error(overlay).

%% The metrics of a registry, each as the list [Name, {Labels, Help}, CLabels, DurationUnit, Data]
%% (ets:match/2), which no list type says
-spec 'prometheus_metric:metrics'(Table :: atom(), registry()) -> [[term()]].
'prometheus_metric:metrics'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_metric_spec
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_metric_spec:registry'(spec()) -> registry().
'prometheus_metric_spec:registry'(_) -> error(overlay).

%% raises missing_metric_spec_key and invalid_metric_name
-spec 'prometheus_metric_spec:name'(spec()) -> name().
'prometheus_metric_spec:name'(_) -> error(overlay).

%% raises invalid_metric_labels and invalid_metric_label_name
-spec 'prometheus_metric_spec:labels'(spec()) -> [label_name()].
'prometheus_metric_spec:labels'(_) -> error(overlay).

%% raises missing_metric_spec_key and invalid_metric_help
-spec 'prometheus_metric_spec:help'(spec()) -> help().
'prometheus_metric_spec:help'(_) -> error(overlay).

%% prometheus_collector:data()
-spec 'prometheus_metric_spec:data'(spec()) -> term().
'prometheus_metric_spec:data'(_) -> error(overlay).

%% the pairs of the map under constant_labels
-spec 'prometheus_metric_spec:constant_labels'(spec()) -> labels().
'prometheus_metric_spec:constant_labels'(_) -> error(overlay).

%% the unit of the spec or of the name of the metric; undefined without one and for duration_unit false
-spec 'prometheus_metric_spec:duration_unit'(spec()) -> duration_unit() | undefined.
'prometheus_metric_spec:duration_unit'(_) -> error(overlay).

-spec 'prometheus_metric_spec:duration_unit_from_spec'(spec()) -> duration_unit() | undefined | false.
'prometheus_metric_spec:duration_unit_from_spec'(_) -> error(overlay).

-spec 'prometheus_metric_spec:extract_common_params'(spec()) ->
          {registry(), name(), Labels :: [label_name()], help(), CLabels :: labels(),
           duration_unit() | undefined, Data :: term()}.
'prometheus_metric_spec:extract_common_params'(_) -> error(overlay).

%% The validate functions take the value of a key of the spec, which is any term
-spec 'prometheus_metric_spec:validate_metric_name'(RawName :: term()) -> name().
'prometheus_metric_spec:validate_metric_name'(_) -> error(overlay).

-spec 'prometheus_metric_spec:validate_metric_name'(RawName :: name(), ListName :: string()) -> name().
'prometheus_metric_spec:validate_metric_name'(_, _) -> error(overlay).

-spec 'prometheus_metric_spec:validate_metric_label_names'(RawLabels :: term()) -> [label_name()].
'prometheus_metric_spec:validate_metric_label_names'(_) -> error(overlay).

-spec 'prometheus_metric_spec:validate_metric_label_name'(RawName :: term()) -> label_name().
'prometheus_metric_spec:validate_metric_label_name'(_) -> error(overlay).

-spec 'prometheus_metric_spec:validate_metric_label_name_content'(string()) -> label_name().
'prometheus_metric_spec:validate_metric_label_name_content'(_) -> error(overlay).

-spec 'prometheus_metric_spec:validate_metric_help'(RawHelp :: term()) -> help().
'prometheus_metric_spec:validate_metric_help'(_) -> error(overlay).

-spec 'prometheus_metric_spec:to_string'(name()) -> string().
'prometheus_metric_spec:to_string'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_misc
%% ---------------------------------------------------------------------------------------------

%% the modules of the loaded applications that have the attribute, with its values
-spec 'prometheus_misc:all_module_attributes'(Name :: atom()) -> [{module(), [term()]}].
'prometheus_misc:all_module_attributes'(_) -> error(overlay).

%% Module:module_info(attributes), [] for a module that cannot be loaded
-spec 'prometheus_misc:module_attributes'(module()) -> [{atom(), [term()]}].
'prometheus_misc:module_attributes'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_sup
%% ---------------------------------------------------------------------------------------------

%% an entry of the default_metrics of the application environment: the metric is counter, gauge,
%% summary, histogram, boolean, or the module of a metric
-type metric_decl() :: {Metric :: atom(), spec()} | {registry(), Metric :: atom(), spec()}.

%% supervisor:startlink_ret(), spelled out: the module prometheus, which calls the function, does not
%% refer to supervisor
-spec 'prometheus_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'prometheus_sup:start_link'() -> error(overlay).

-spec 'prometheus_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'prometheus_sup:init'(_) -> error(overlay).

-spec 'prometheus_sup:create_tables'() -> ok.
'prometheus_sup:create_tables'() -> error(overlay).

-spec 'prometheus_sup:register_collectors'() -> ok.
'prometheus_sup:register_collectors'() -> error(overlay).

%% what declare/1 of the metric modules gives, for each default metric
-spec 'prometheus_sup:register_metrics'() -> [boolean()].
'prometheus_sup:register_metrics'() -> error(overlay).

-spec 'prometheus_sup:register_metrics'([metric_decl()]) -> [boolean()].
'prometheus_sup:register_metrics'(_) -> error(overlay).

-spec 'prometheus_sup:setup_instrumenters'() -> [ok].
'prometheus_sup:setup_instrumenters'() -> error(overlay).

-spec 'prometheus_sup:default_metrics'() -> [metric_decl()].
'prometheus_sup:default_metrics'() -> error(overlay).

%% the table, or ok when it exists already
-spec 'prometheus_sup:maybe_create_table'(Name :: atom(), {set | bag, Concurrency} | Concurrency) ->
          ets:table() | ok when Concurrency :: read_concurrency | write_concurrency.
'prometheus_sup:maybe_create_table'(_, _) -> error(overlay).

-spec 'prometheus_sup:declare_metric'(metric_decl()) -> boolean().
'prometheus_sup:declare_metric'(_) -> error(overlay).

-spec 'prometheus_sup:declare_metric'(Metric :: atom(), spec()) -> boolean().
'prometheus_sup:declare_metric'(_, _) -> error(overlay).

-spec 'prometheus_sup:type_to_module'(atom()) -> module().
'prometheus_sup:type_to_module'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_time
%% ---------------------------------------------------------------------------------------------

%% the unit that the name of a metric ends with
-spec 'prometheus_time:duration_unit_from_string'(string()) -> duration_unit() | undefined.
'prometheus_time:duration_unit_from_string'(_) -> error(overlay).

%% the value of duration_unit of a spec, any term; raises invalid_value for an unknown unit
-spec 'prometheus_time:validate_duration_unit'(term()) -> duration_unit() | undefined | false.
'prometheus_time:validate_duration_unit'(_) -> error(overlay).

%% a bound of a bucket, in the unit of the metric, to native time units
-spec 'prometheus_time:maybe_convert_to_native'(duration_unit() | undefined, infinity) -> infinity
                                             ; (duration_unit() | undefined, number()) -> number().
'prometheus_time:maybe_convert_to_native'(_, _) -> error(overlay).

%% a sum of native time units to the unit of the metric
-spec 'prometheus_time:maybe_convert_to_du'(duration_unit() | undefined, infinity) -> infinity
                                         ; (duration_unit() | undefined, number()) -> number().
'prometheus_time:maybe_convert_to_du'(_, _) -> error(overlay).

-spec 'prometheus_time:duration_unit_from_string'(string(), [{string(), duration_unit()}]) ->
          duration_unit() | undefined.
'prometheus_time:duration_unit_from_string'(_, _) -> error(overlay).

%% native time units to nanoseconds
-spec 'prometheus_time:from_native'(number()) -> integer().
'prometheus_time:from_native'(_) -> error(overlay).

-spec 'prometheus_time:from_native'(number(), duration_unit()) -> float().
'prometheus_time:from_native'(_, _) -> error(overlay).

%% nanoseconds to native time units
-spec 'prometheus_time:to_native'(number()) -> integer().
'prometheus_time:to_native'(_) -> error(overlay).

-spec 'prometheus_time:to_native'(number(), duration_unit()) -> integer().
'prometheus_time:to_native'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_boolean
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_boolean:new'(spec()) -> ok.
'prometheus_boolean:new'(_) -> error(overlay).

%% false if the boolean exists already
-spec 'prometheus_boolean:declare'(spec()) -> boolean().
'prometheus_boolean:declare'(_) -> error(overlay).

-spec 'prometheus_boolean:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_boolean:deregister'(_) -> error(overlay).

%% was the boolean registered, and was a series of it removed
-spec 'prometheus_boolean:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_boolean:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a boolean without labels
-spec 'prometheus_boolean:set_default'(registry(), name()) -> ok.
'prometheus_boolean:set_default'(_, _) -> error(overlay).

-spec 'prometheus_boolean:set'(name(), bool_value()) -> ok.
'prometheus_boolean:set'(_, _) -> error(overlay).

-spec 'prometheus_boolean:set'(name(), label_values(), bool_value()) -> ok.
'prometheus_boolean:set'(_, _, _) -> error(overlay).

%% true, a number above 0 and a non-empty list set the boolean to true; raises invalid_value for other terms
-spec 'prometheus_boolean:set'(registry(), name(), label_values(), bool_value()) -> ok.
'prometheus_boolean:set'(_, _, _, _) -> error(overlay).

-spec 'prometheus_boolean:toggle'(name()) -> ok.
'prometheus_boolean:toggle'(_) -> error(overlay).

-spec 'prometheus_boolean:toggle'(name(), label_values()) -> ok.
'prometheus_boolean:toggle'(_, _) -> error(overlay).

%% raises invalid_value for a boolean that is undefined
-spec 'prometheus_boolean:toggle'(registry(), name(), label_values()) -> ok.
'prometheus_boolean:toggle'(_, _, _) -> error(overlay).

-spec 'prometheus_boolean:remove'(name()) -> boolean().
'prometheus_boolean:remove'(_) -> error(overlay).

-spec 'prometheus_boolean:remove'(name(), label_values()) -> boolean().
'prometheus_boolean:remove'(_, _) -> error(overlay).

-spec 'prometheus_boolean:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_boolean:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_boolean:reset'(name()) -> boolean().
'prometheus_boolean:reset'(_) -> error(overlay).

-spec 'prometheus_boolean:reset'(name(), label_values()) -> boolean().
'prometheus_boolean:reset'(_, _) -> error(overlay).

-spec 'prometheus_boolean:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_boolean:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_boolean:value'(name()) -> boolean() | undefined.
'prometheus_boolean:value'(_) -> error(overlay).

-spec 'prometheus_boolean:value'(name(), label_values()) -> boolean() | undefined.
'prometheus_boolean:value'(_, _) -> error(overlay).

%% undefined if there is no series for the label values
-spec 'prometheus_boolean:value'(registry(), name(), label_values()) -> boolean() | undefined.
'prometheus_boolean:value'(_, _, _) -> error(overlay).

%% a boolean that is undefined shows as false
-spec 'prometheus_boolean:values'(registry(), name()) -> [{series_labels(), boolean()}].
'prometheus_boolean:values'(_, _) -> error(overlay).

-spec 'prometheus_boolean:deregister_cleanup'(registry()) -> ok.
'prometheus_boolean:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_boolean:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_boolean:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_boolean:collect_metrics'(name(), collect_data()) -> [prometheus_model:'Metric'()].
'prometheus_boolean:collect_metrics'(_, _) -> error(overlay).

-spec 'prometheus_boolean:deregister_select'(registry(), name()) -> ets:match_spec().
'prometheus_boolean:deregister_select'(_, _) -> error(overlay).

%% the row of a series is {{Registry, Name, LabelValues}, 0 | 1 | undefined}
-spec 'prometheus_boolean:set_'(registry(), name(), label_values(), Value :: 0 | 1 | undefined) -> ok.
'prometheus_boolean:set_'(_, _, _, _) -> error(overlay).

-spec 'prometheus_boolean:save_toggle'(registry(), name(), label_values()) -> ok.
'prometheus_boolean:save_toggle'(_, _, _) -> error(overlay).

%% the fun is called if another process has inserted the series meanwhile
-spec 'prometheus_boolean:insert_metric'(registry(), name(), label_values(), Value,
                                         ConflictCB :: fun((registry(), name(), label_values(), Value) -> ok)) -> ok
              when Value :: 0 | 1 | undefined.
'prometheus_boolean:insert_metric'(_, _, _, _, _) -> error(overlay).

-spec 'prometheus_boolean:load_all_values'(registry(), name()) -> [[term()]].
'prometheus_boolean:load_all_values'(_, _) -> error(overlay).

-spec 'prometheus_boolean:create_boolean'(name(), help(), collect_data()) -> prometheus_model:'MetricFamily'().
'prometheus_boolean:create_boolean'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_counter
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_counter:new'(spec()) -> ok.
'prometheus_counter:new'(_) -> error(overlay).

%% false if the counter exists already
-spec 'prometheus_counter:declare'(spec()) -> boolean().
'prometheus_counter:declare'(_) -> error(overlay).

-spec 'prometheus_counter:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_counter:deregister'(_) -> error(overlay).

%% was the counter registered, and was a series of it removed
-spec 'prometheus_counter:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_counter:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a counter without labels
-spec 'prometheus_counter:set_default'(registry(), name()) -> boolean().
'prometheus_counter:set_default'(_, _) -> error(overlay).

-spec 'prometheus_counter:inc'(name()) -> ok.
'prometheus_counter:inc'(_) -> error(overlay).

%% the second argument is the label values if it is a list, else the value
-spec 'prometheus_counter:inc'(name(), label_values() | number()) -> ok.
'prometheus_counter:inc'(_, _) -> error(overlay).

-spec 'prometheus_counter:inc'(name(), label_values(), Value :: number()) -> ok.
'prometheus_counter:inc'(_, _, _) -> error(overlay).

%% raises invalid_value for what is not a non-negative number
-spec 'prometheus_counter:inc'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_counter:inc'(_, _, _, _) -> error(overlay).

-spec 'prometheus_counter:remove'(name()) -> boolean().
'prometheus_counter:remove'(_) -> error(overlay).

-spec 'prometheus_counter:remove'(name(), label_values()) -> boolean().
'prometheus_counter:remove'(_, _) -> error(overlay).

-spec 'prometheus_counter:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_counter:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_counter:reset'(name()) -> boolean().
'prometheus_counter:reset'(_) -> error(overlay).

-spec 'prometheus_counter:reset'(name(), label_values()) -> boolean().
'prometheus_counter:reset'(_, _) -> error(overlay).

-spec 'prometheus_counter:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_counter:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_counter:value'(name()) -> number() | undefined.
'prometheus_counter:value'(_) -> error(overlay).

-spec 'prometheus_counter:value'(name(), label_values()) -> number() | undefined.
'prometheus_counter:value'(_, _) -> error(overlay).

%% undefined if there is no series for the label values
-spec 'prometheus_counter:value'(registry(), name(), label_values()) -> number() | undefined.
'prometheus_counter:value'(_, _, _) -> error(overlay).

-spec 'prometheus_counter:values'(registry(), name()) -> [{series_labels(), number()}].
'prometheus_counter:values'(_, _) -> error(overlay).

-spec 'prometheus_counter:deregister_cleanup'(registry()) -> ok.
'prometheus_counter:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_counter:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_counter:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_counter:collect_metrics'(name(), collect_data()) -> [prometheus_model:'Metric'()].
'prometheus_counter:collect_metrics'(_, _) -> error(overlay).

-spec 'prometheus_counter:deregister_select'(registry(), name()) -> ets:match_spec().
'prometheus_counter:deregister_select'(_, _) -> error(overlay).

%% the fun is called if another process has inserted the series meanwhile
-spec 'prometheus_counter:insert_metric'(registry(), name(), label_values(), Value :: number(),
                                         ConflictCB :: fun((registry(), name(), label_values(), number()) -> ok)) -> ok.
'prometheus_counter:insert_metric'(_, _, _, _, _) -> error(overlay).

%% the rows {{Registry, Name, LabelValues, Scheduler}, ISum, FSum} as [LabelValues, ISum, FSum]
-spec 'prometheus_counter:load_all_values'(registry(), name()) -> [[term()]].
'prometheus_counter:load_all_values'(_, _) -> error(overlay).

-spec 'prometheus_counter:schedulers_seq'() -> [non_neg_integer()].
'prometheus_counter:schedulers_seq'() -> error(overlay).

-spec 'prometheus_counter:key'(registry(), name(), label_values()) -> skey().
'prometheus_counter:key'(_, _, _) -> error(overlay).

%% the sum over the schedulers for each list of label values
-spec 'prometheus_counter:reduce_label_values'(MFValues :: [[term()]]) -> #{label_values() => number()}.
'prometheus_counter:reduce_label_values'(_) -> error(overlay).

-spec 'prometheus_counter:serialize_label_values'(fun((series_labels(), Value :: number()) -> T), [label_name()],
                                                  #{label_values() => number()}) -> [T].
'prometheus_counter:serialize_label_values'(_, _, _) -> error(overlay).

-spec 'prometheus_counter:create_counter'(name(), help(), collect_data()) -> prometheus_model:'MetricFamily'().
'prometheus_counter:create_counter'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_gauge
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_gauge:new'(spec()) -> ok.
'prometheus_gauge:new'(_) -> error(overlay).

%% false if the gauge exists already
-spec 'prometheus_gauge:declare'(spec()) -> boolean().
'prometheus_gauge:declare'(_) -> error(overlay).

-spec 'prometheus_gauge:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_gauge:deregister'(_) -> error(overlay).

%% was the gauge registered, and was a series of it removed
-spec 'prometheus_gauge:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_gauge:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a gauge without labels
-spec 'prometheus_gauge:set_default'(registry(), name()) -> boolean().
'prometheus_gauge:set_default'(_, _) -> error(overlay).

-spec 'prometheus_gauge:set'(name(), number() | undefined) -> ok.
'prometheus_gauge:set'(_, _) -> error(overlay).

-spec 'prometheus_gauge:set'(name(), label_values(), number() | undefined) -> ok.
'prometheus_gauge:set'(_, _, _) -> error(overlay).

%% raises invalid_value for what is neither a number nor undefined
-spec 'prometheus_gauge:set'(registry(), name(), label_values(), number() | undefined) -> ok.
'prometheus_gauge:set'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:inc'(name()) -> ok.
'prometheus_gauge:inc'(_) -> error(overlay).

%% the second argument is the label values if it is a list, else the value
-spec 'prometheus_gauge:inc'(name(), label_values() | number()) -> ok.
'prometheus_gauge:inc'(_, _) -> error(overlay).

-spec 'prometheus_gauge:inc'(name(), label_values(), Value :: number()) -> ok.
'prometheus_gauge:inc'(_, _, _) -> error(overlay).

%% raises invalid_value for what is not a number, invalid_operation for a gauge that is undefined
-spec 'prometheus_gauge:inc'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_gauge:inc'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:dec'(name()) -> ok.
'prometheus_gauge:dec'(_) -> error(overlay).

%% the second argument is the label values if it is a list, else the value
-spec 'prometheus_gauge:dec'(name(), label_values() | number()) -> ok.
'prometheus_gauge:dec'(_, _) -> error(overlay).

-spec 'prometheus_gauge:dec'(name(), label_values(), Value :: number()) -> ok.
'prometheus_gauge:dec'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:dec'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_gauge:dec'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:set_to_current_time'(name()) -> ok.
'prometheus_gauge:set_to_current_time'(_) -> error(overlay).

-spec 'prometheus_gauge:set_to_current_time'(name(), label_values()) -> ok.
'prometheus_gauge:set_to_current_time'(_, _) -> error(overlay).

-spec 'prometheus_gauge:set_to_current_time'(registry(), name(), label_values()) -> ok.
'prometheus_gauge:set_to_current_time'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:track_inprogress'(name(), fun(() -> T)) -> T.
'prometheus_gauge:track_inprogress'(_, _) -> error(overlay).

-spec 'prometheus_gauge:track_inprogress'(name(), label_values(), fun(() -> T)) -> T.
'prometheus_gauge:track_inprogress'(_, _, _) -> error(overlay).

%% the gauge counts the calls of the fun that are running; gives the result of the fun
-spec 'prometheus_gauge:track_inprogress'(registry(), name(), label_values(), fun(() -> T)) -> T.
'prometheus_gauge:track_inprogress'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:set_duration'(name(), fun(() -> T)) -> T.
'prometheus_gauge:set_duration'(_, _) -> error(overlay).

-spec 'prometheus_gauge:set_duration'(name(), label_values(), fun(() -> T)) -> T.
'prometheus_gauge:set_duration'(_, _, _) -> error(overlay).

%% sets the gauge to the time that the fun takes, in native units, and gives the result of the fun
-spec 'prometheus_gauge:set_duration'(registry(), name(), label_values(), fun(() -> T)) -> T.
'prometheus_gauge:set_duration'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:remove'(name()) -> boolean().
'prometheus_gauge:remove'(_) -> error(overlay).

-spec 'prometheus_gauge:remove'(name(), label_values()) -> boolean().
'prometheus_gauge:remove'(_, _) -> error(overlay).

-spec 'prometheus_gauge:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_gauge:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:reset'(name()) -> boolean().
'prometheus_gauge:reset'(_) -> error(overlay).

-spec 'prometheus_gauge:reset'(name(), label_values()) -> boolean().
'prometheus_gauge:reset'(_, _) -> error(overlay).

-spec 'prometheus_gauge:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_gauge:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:value'(name()) -> number() | undefined.
'prometheus_gauge:value'(_) -> error(overlay).

-spec 'prometheus_gauge:value'(name(), label_values()) -> number() | undefined.
'prometheus_gauge:value'(_, _) -> error(overlay).

%% undefined if there is no series for the label values, or if the gauge was set to undefined
-spec 'prometheus_gauge:value'(registry(), name(), label_values()) -> number() | undefined.
'prometheus_gauge:value'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:values'(registry(), name()) -> [{series_labels(), number() | undefined}].
'prometheus_gauge:values'(_, _) -> error(overlay).

-spec 'prometheus_gauge:deregister_cleanup'(registry()) -> ok.
'prometheus_gauge:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_gauge:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_gauge:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_gauge:collect_metrics'(name(), collect_data_du()) -> [prometheus_model:'Metric'()].
'prometheus_gauge:collect_metrics'(_, _) -> error(overlay).

%% the row of a series is {Key, IValue, FValue}; both values are undefined after set/4 with undefined
-spec 'prometheus_gauge:key'(registry(), name(), label_values()) -> {registry(), name(), label_values()}.
'prometheus_gauge:key'(_, _, _) -> error(overlay).

-spec 'prometheus_gauge:maybe_insert_metric_for_inc'(registry(), name(), label_values(), Value :: integer()) -> ok.
'prometheus_gauge:maybe_insert_metric_for_inc'(_, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:deregister_select'(registry(), name()) -> ets:match_spec().
'prometheus_gauge:deregister_select'(_, _) -> error(overlay).

%% the fun is called if another process has inserted the series meanwhile
-spec 'prometheus_gauge:insert_metric'(registry(), name(), label_values(), Value,
                                       ConflictCB :: fun((registry(), name(), label_values(), Value) -> ok)) -> ok
              when Value :: number() | undefined.
'prometheus_gauge:insert_metric'(_, _, _, _, _) -> error(overlay).

-spec 'prometheus_gauge:load_all_values'(registry(), name()) -> [[term()]].
'prometheus_gauge:load_all_values'(_, _) -> error(overlay).

%% the value of a row {Key, IValue, FValue}
-spec 'prometheus_gauge:sum'(number(), number()) -> number()
                       ; (number() | undefined, undefined) -> undefined.
'prometheus_gauge:sum'(_, _) -> error(overlay).

-spec 'prometheus_gauge:create_gauge'(name(), help(), collect_data_du()) -> prometheus_model:'MetricFamily'().
'prometheus_gauge:create_gauge'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_histogram
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_histogram:new'(spec()) -> ok.
'prometheus_histogram:new'(_) -> error(overlay).

%% false if the histogram exists already
-spec 'prometheus_histogram:declare'(spec()) -> boolean().
'prometheus_histogram:declare'(_) -> error(overlay).

-spec 'prometheus_histogram:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_histogram:deregister'(_) -> error(overlay).

%% was the histogram registered, and was a series of it removed
-spec 'prometheus_histogram:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_histogram:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a histogram without labels
-spec 'prometheus_histogram:set_default'(registry(), name()) -> boolean().
'prometheus_histogram:set_default'(_, _) -> error(overlay).

-spec 'prometheus_histogram:observe'(name(), Value :: number()) -> ok.
'prometheus_histogram:observe'(_, _) -> error(overlay).

-spec 'prometheus_histogram:observe'(name(), label_values(), Value :: number()) -> ok.
'prometheus_histogram:observe'(_, _, _) -> error(overlay).

%% raises invalid_value for what is not a number
-spec 'prometheus_histogram:observe'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_histogram:observe'(_, _, _, _) -> error(overlay).

%% observe/4 for a caller that knows the bounds, in native units, and the position of the bucket
-spec 'prometheus_histogram:pobserve'(registry(), name(), label_values(), Buckets :: buckets(),
                                      BucketPos :: non_neg_integer(), Value :: number()) -> ok.
'prometheus_histogram:pobserve'(_, _, _, _, _, _) -> error(overlay).

-spec 'prometheus_histogram:observe_duration'(name(), fun(() -> T)) -> T.
'prometheus_histogram:observe_duration'(_, _) -> error(overlay).

-spec 'prometheus_histogram:observe_duration'(name(), label_values(), fun(() -> T)) -> T.
'prometheus_histogram:observe_duration'(_, _, _) -> error(overlay).

%% observes the time that the fun takes, in native units, and gives its result
-spec 'prometheus_histogram:observe_duration'(registry(), name(), label_values(), fun(() -> T)) -> T.
'prometheus_histogram:observe_duration'(_, _, _, _) -> error(overlay).

-spec 'prometheus_histogram:remove'(name()) -> boolean().
'prometheus_histogram:remove'(_) -> error(overlay).

-spec 'prometheus_histogram:remove'(name(), label_values()) -> boolean().
'prometheus_histogram:remove'(_, _) -> error(overlay).

-spec 'prometheus_histogram:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_histogram:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:reset'(name()) -> boolean().
'prometheus_histogram:reset'(_) -> error(overlay).

-spec 'prometheus_histogram:reset'(name(), label_values()) -> boolean().
'prometheus_histogram:reset'(_, _) -> error(overlay).

-spec 'prometheus_histogram:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_histogram:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:value'(name()) -> {Buckets :: [number(), ...], Sum :: number()} | undefined.
'prometheus_histogram:value'(_) -> error(overlay).

-spec 'prometheus_histogram:value'(name(), label_values()) ->
          {Buckets :: [number(), ...], Sum :: number()} | undefined.
'prometheus_histogram:value'(_, _) -> error(overlay).

%% prometheus_metric:histogram_value(): the counters of the buckets and the sum; undefined if there is no
%% series for the label values
-spec 'prometheus_histogram:value'(registry(), name(), label_values()) ->
          {Buckets :: [number(), ...], Sum :: number()} | undefined.
'prometheus_histogram:value'(_, _, _) -> error(overlay).

%% for each series the bounds with the counters of their buckets, and the sum
-spec 'prometheus_histogram:values'(registry(), name()) ->
          [{series_labels(), [{bucket_bound(), number()}], Sum :: number()}].
'prometheus_histogram:values'(_, _) -> error(overlay).

-spec 'prometheus_histogram:buckets'(name()) -> buckets().
'prometheus_histogram:buckets'(_) -> error(overlay).

-spec 'prometheus_histogram:buckets'(name(), label_values()) -> buckets().
'prometheus_histogram:buckets'(_, _) -> error(overlay).

%% the bounds of the histogram, in the unit of the metric
-spec 'prometheus_histogram:buckets'(registry(), name(), label_values()) -> buckets().
'prometheus_histogram:buckets'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:deregister_cleanup'(registry()) -> ok.
'prometheus_histogram:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_histogram:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_histogram:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_histogram:collect_metrics'(name(), collect_data_du(buckets())) -> [prometheus_model:'Metric'()].
'prometheus_histogram:collect_metrics'(_, _) -> error(overlay).

%% the spec with the buckets under the key data; raises no_buckets, invalid_buckets, invalid_bound
-spec 'prometheus_histogram:validate_histogram_spec'(spec()) -> spec().
'prometheus_histogram:validate_histogram_spec'(_) -> error(overlay).

-spec 'prometheus_histogram:validate_histogram_labels'([label_name()]) -> [label_name()].
'prometheus_histogram:validate_histogram_labels'(_) -> error(overlay).

-spec 'prometheus_histogram:raise_error_if_le_label_found'(label_name()) -> label_name().
'prometheus_histogram:raise_error_if_le_label_found'(_) -> error(overlay).

%% inserts the row of the series and calls the fun
-spec 'prometheus_histogram:insert_metric'(registry(), name(), label_values(), Value :: number(),
                                           CB :: fun((registry(), name(), label_values(), number()) -> T)) -> T.
'prometheus_histogram:insert_metric'(_, _, _, _, _) -> error(overlay).

%% The row of a series is {Key, NBounds, ISum, FSum, Bucket1, Bucket2, ...}, the bounds in native units and a
%% counter for each: a tuple whose size depends on the metric. Gives what ets:select_replace/2 gives
-spec 'prometheus_histogram:fobserve_impl'(skey(), Metric :: tuple(), Value :: number()) -> non_neg_integer().
'prometheus_histogram:fobserve_impl'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:fobserve_impl'(skey(), Buckets :: buckets(), BucketPos :: non_neg_integer(),
                                         Value :: number()) -> non_neg_integer().
'prometheus_histogram:fobserve_impl'(_, _, _, _) -> error(overlay).

-spec 'prometheus_histogram:insert_placeholders'(registry(), name(), label_values()) -> boolean().
'prometheus_histogram:insert_placeholders'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:calculate_histogram_bucket_position'(Metric :: tuple(), Value :: number()) ->
          non_neg_integer().
'prometheus_histogram:calculate_histogram_bucket_position'(_, _) -> error(overlay).

-spec 'prometheus_histogram:generate_select_replace'(skey(), Bounds :: buckets(), BucketPos :: non_neg_integer(),
                                                   Value :: number()) -> ets:match_spec().
'prometheus_histogram:generate_select_replace'(_, _, _, _) -> error(overlay).

%% the positions of the counters in the row
-spec 'prometheus_histogram:buckets_seq'(buckets()) -> [pos_integer()].
'prometheus_histogram:buckets_seq'(_) -> error(overlay).

-spec 'prometheus_histogram:generate_update_spec'(buckets()) -> [{pos_integer(), 0}].
'prometheus_histogram:generate_update_spec'(_) -> error(overlay).

%% the match variable '$Index'
-spec 'prometheus_histogram:gen_query_placeholder'(Index :: pos_integer()) -> atom().
'prometheus_histogram:gen_query_placeholder'(_) -> error(overlay).

-spec 'prometheus_histogram:gen_query_bound_placeholders'(buckets()) -> [atom()].
'prometheus_histogram:gen_query_bound_placeholders'(_) -> error(overlay).

%% the cumulative counters
-spec 'prometheus_histogram:augment_counters'([number(), ...]) -> [number(), ...].
'prometheus_histogram:augment_counters'(_) -> error(overlay).

-spec 'prometheus_histogram:augment_counters'(Counters :: [number()], LAcc :: [number(), ...], CAcc :: number()) ->
          [number(), ...].
'prometheus_histogram:augment_counters'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:metric_buckets'(Metric :: tuple()) -> buckets().
'prometheus_histogram:metric_buckets'(_) -> error(overlay).

%% the counters of the buckets, summed over the rows of the schedulers
-spec 'prometheus_histogram:reduce_buckets_counters'(Metrics :: [tuple()]) -> [number()].
'prometheus_histogram:reduce_buckets_counters'(_) -> error(overlay).

-spec 'prometheus_histogram:transpose'([[T]]) -> [[T]].
'prometheus_histogram:transpose'(_) -> error(overlay).

-spec 'prometheus_histogram:reduce_sum'(Metrics :: [tuple()]) -> number().
'prometheus_histogram:reduce_sum'(_) -> error(overlay).

-spec 'prometheus_histogram:reduce_sum'(mf(), Metrics :: [tuple()]) -> number().
'prometheus_histogram:reduce_sum'(_, _) -> error(overlay).

%% Stat is [ISum, FSum, Bucket1, Bucket2, ...]
-spec 'prometheus_histogram:create_histogram_metric'(CLabels :: labels(), [label_name()], duration_unit() | undefined,
                                                     Bounds :: buckets(), label_values(), Stat :: [number()]) ->
          prometheus_model:'Metric'().
'prometheus_histogram:create_histogram_metric'(_, _, _, _, _, _) -> error(overlay).

%% the rows as [LabelValues, ISum, FSum, Bucket1, Bucket2, ...]
-spec 'prometheus_histogram:load_all_values'(registry(), name(), Bounds :: buckets()) -> [[term()]].
'prometheus_histogram:load_all_values'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:deregister_select'(registry(), name(), Buckets :: buckets()) -> ets:match_spec().
'prometheus_histogram:deregister_select'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:delete_metrics'(registry(), Buckets :: buckets()) -> true.
'prometheus_histogram:delete_metrics'(_, _) -> error(overlay).

%% the elements from Pos to End - 1
-spec 'prometheus_histogram:sub_tuple_to_list'(tuple(), Pos :: pos_integer(), End :: pos_integer()) -> [term()].
'prometheus_histogram:sub_tuple_to_list'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:schedulers_seq'() -> [non_neg_integer()].
'prometheus_histogram:schedulers_seq'() -> error(overlay).

-spec 'prometheus_histogram:key'(registry(), name(), label_values()) -> skey().
'prometheus_histogram:key'(_, _, _) -> error(overlay).

%% the sums over the schedulers, [ISum, FSum, Bucket1, ...], for each list of label values
-spec 'prometheus_histogram:reduce_label_values'(MFValues :: [[term()]]) -> #{label_values() => [number()]}.
'prometheus_histogram:reduce_label_values'(_) -> error(overlay).

-spec 'prometheus_histogram:mf_values'(registry(), name(), mf()) ->
          [{series_labels(), [{bucket_bound(), number()}], Sum :: number()}].
'prometheus_histogram:mf_values'(_, _, _) -> error(overlay).

-spec 'prometheus_histogram:create_histogram'(name(), help(), collect_data_du(buckets())) ->
          prometheus_model:'MetricFamily'().
'prometheus_histogram:create_histogram'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_quantile_summary
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_quantile_summary:new'(spec()) -> ok.
'prometheus_quantile_summary:new'(_) -> error(overlay).

%% false if the summary exists already
-spec 'prometheus_quantile_summary:declare'(spec()) -> boolean().
'prometheus_quantile_summary:declare'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_quantile_summary:deregister'(_) -> error(overlay).

%% was the summary registered, and was a series of it removed
-spec 'prometheus_quantile_summary:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_quantile_summary:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a summary without labels
-spec 'prometheus_quantile_summary:set_default'(registry(), name()) -> boolean().
'prometheus_quantile_summary:set_default'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:observe'(name(), Value :: number()) -> ok.
'prometheus_quantile_summary:observe'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:observe'(name(), label_values(), Value :: number()) -> ok.
'prometheus_quantile_summary:observe'(_, _, _) -> error(overlay).

%% raises invalid_value for what is not a number
-spec 'prometheus_quantile_summary:observe'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_quantile_summary:observe'(_, _, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:observe_duration'(name(), fun(() -> T)) -> T.
'prometheus_quantile_summary:observe_duration'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:observe_duration'(name(), label_values(), fun(() -> T)) -> T.
'prometheus_quantile_summary:observe_duration'(_, _, _) -> error(overlay).

%% observes the time that the fun takes, in native units, and gives its result
-spec 'prometheus_quantile_summary:observe_duration'(registry(), name(), label_values(), fun(() -> T)) -> T.
'prometheus_quantile_summary:observe_duration'(_, _, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:remove'(name()) -> boolean().
'prometheus_quantile_summary:remove'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:remove'(name(), label_values()) -> boolean().
'prometheus_quantile_summary:remove'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_quantile_summary:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:reset'(name()) -> boolean().
'prometheus_quantile_summary:reset'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:reset'(name(), label_values()) -> boolean().
'prometheus_quantile_summary:reset'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_quantile_summary:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:value'(name()) ->
          {Count :: number(), Sum :: number(), Quantiles :: [{float(), number()}]} | undefined.
'prometheus_quantile_summary:value'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:value'(name(), label_values()) ->
          {Count :: number(), Sum :: number(), Quantiles :: [{float(), number()}]} | undefined.
'prometheus_quantile_summary:value'(_, _) -> error(overlay).

%% count, sum and the values of the quantiles of the targets; undefined if there is no series for the label values
-spec 'prometheus_quantile_summary:value'(registry(), name(), label_values()) ->
          {Count :: number(), Sum :: number(), Quantiles :: [{float(), number()}]} | undefined.
'prometheus_quantile_summary:value'(_, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:values'(registry(), name()) ->
          [{series_labels(), Count :: number(), Sum :: number(), Quantiles :: [{float(), number()}]}].
'prometheus_quantile_summary:values'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:deregister_cleanup'(registry()) -> ok.
'prometheus_quantile_summary:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_quantile_summary:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_quantile_summary:collect_metrics'(name(), collect_data_du(qs_config())) ->
          [prometheus_model:'Metric'()].
'prometheus_quantile_summary:collect_metrics'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:deregister_select'(registry(), name()) -> ets:match_spec().
'prometheus_quantile_summary:deregister_select'(_, _) -> error(overlay).

%% the spec with the configuration under the key data; raises invalid_targets
-spec 'prometheus_quantile_summary:validate_summary_spec'(spec()) -> spec().
'prometheus_quantile_summary:validate_summary_spec'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:validate_summary_labels'([label_name()]) -> [label_name()].
'prometheus_quantile_summary:validate_summary_labels'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:raise_error_if_quantile_label_found'(label_name()) -> label_name().
'prometheus_quantile_summary:raise_error_if_quantile_label_found'(_) -> error(overlay).

%% the fun is called if another process has inserted the series meanwhile
-spec 'prometheus_quantile_summary:insert_metric'(registry(), name(), label_values(), Value :: number(),
                                                  ConflictCB :: fun((registry(), name(), label_values(), number()) -> ok)) ->
          ok.
'prometheus_quantile_summary:insert_metric'(_, _, _, _, _) -> error(overlay).

%% the rows {Key, Count, Sum, Estimator, CompressLimit} as [LabelValues, Count, Sum, Estimator]
-spec 'prometheus_quantile_summary:load_all_values'(registry(), name()) -> [[term()]].
'prometheus_quantile_summary:load_all_values'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:get_configuration'(registry(), name()) -> qs_config().
'prometheus_quantile_summary:get_configuration'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:schedulers_seq'() -> [non_neg_integer()].
'prometheus_quantile_summary:schedulers_seq'() -> error(overlay).

-spec 'prometheus_quantile_summary:key'(registry(), name(), label_values()) -> skey().
'prometheus_quantile_summary:key'(_, _, _) -> error(overlay).

%% the rows of the schedulers for one series, each as [Count, Sum, Estimator]: not empty
-spec 'prometheus_quantile_summary:reduce_values'(Values :: [[number() | estimator()]]) ->
          {Count :: number(), Sum :: number(), estimator()}.
'prometheus_quantile_summary:reduce_values'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:create_summary'(name(), help(), collect_data_du(qs_config())) ->
          prometheus_model:'MetricFamily'().
'prometheus_quantile_summary:create_summary'(_, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:default_compress_limit'() -> pos_integer().
'prometheus_quantile_summary:default_compress_limit'() -> error(overlay).

-spec 'prometheus_quantile_summary:invariant_and_quantiles_from_spec'(spec()) -> {invariant(), QNs :: [float()]}.
'prometheus_quantile_summary:invariant_and_quantiles_from_spec'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:compress_limit_from_spec'(spec()) -> integer().
'prometheus_quantile_summary:compress_limit_from_spec'(_) -> error(overlay).

%% the value of targets of the spec, any term; raises invalid_targets
-spec 'prometheus_quantile_summary:validate_targets'(Targets :: term()) -> ok.
'prometheus_quantile_summary:validate_targets'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:default_targets'() -> [{Quantile :: float(), Error :: float()}, ...].
'prometheus_quantile_summary:default_targets'() -> error(overlay).

%% an empty estimator
-spec 'prometheus_quantile_summary:quantile'(qs_config()) -> estimator().
'prometheus_quantile_summary:quantile'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:quantile'(qs_config(), Val :: number()) -> estimator().
'prometheus_quantile_summary:quantile'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:quantile_add'(estimator(), Val :: number(), CompressLimit :: integer()) ->
          estimator().
'prometheus_quantile_summary:quantile_add'(_, _, _) -> error(overlay).

-spec 'prometheus_quantile_summary:quantile_values'(estimator(), QNs :: [float()]) -> [{float(), number()}].
'prometheus_quantile_summary:quantile_values'(_, _) -> error(overlay).

-spec 'prometheus_quantile_summary:fold_quantiles'([estimator(), ...]) -> estimator().
'prometheus_quantile_summary:fold_quantiles'(_) -> error(overlay).

-spec 'prometheus_quantile_summary:quantile_merge'(estimator(), estimator()) -> estimator().
'prometheus_quantile_summary:quantile_merge'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_summary
%% ---------------------------------------------------------------------------------------------

%% raises mf_already_exists, and what the keys of the spec raise
-spec 'prometheus_summary:new'(spec()) -> ok.
'prometheus_summary:new'(_) -> error(overlay).

%% false if the summary exists already
-spec 'prometheus_summary:declare'(spec()) -> boolean().
'prometheus_summary:declare'(_) -> error(overlay).

-spec 'prometheus_summary:deregister'(name()) -> {boolean(), boolean()}.
'prometheus_summary:deregister'(_) -> error(overlay).

%% was the summary registered, and was a series of it removed
-spec 'prometheus_summary:deregister'(registry(), name()) -> {boolean(), boolean()}.
'prometheus_summary:deregister'(_, _) -> error(overlay).

%% callback of prometheus_metric: the series of a summary without labels
-spec 'prometheus_summary:set_default'(registry(), name()) -> boolean().
'prometheus_summary:set_default'(_, _) -> error(overlay).

-spec 'prometheus_summary:observe'(name(), Value :: number()) -> ok.
'prometheus_summary:observe'(_, _) -> error(overlay).

-spec 'prometheus_summary:observe'(name(), label_values(), Value :: number()) -> ok.
'prometheus_summary:observe'(_, _, _) -> error(overlay).

%% raises invalid_value for what is not a number
-spec 'prometheus_summary:observe'(registry(), name(), label_values(), Value :: number()) -> ok.
'prometheus_summary:observe'(_, _, _, _) -> error(overlay).

-spec 'prometheus_summary:observe_duration'(name(), fun(() -> T)) -> T.
'prometheus_summary:observe_duration'(_, _) -> error(overlay).

-spec 'prometheus_summary:observe_duration'(name(), label_values(), fun(() -> T)) -> T.
'prometheus_summary:observe_duration'(_, _, _) -> error(overlay).

%% observes the time that the fun takes, in native units, and gives its result
-spec 'prometheus_summary:observe_duration'(registry(), name(), label_values(), fun(() -> T)) -> T.
'prometheus_summary:observe_duration'(_, _, _, _) -> error(overlay).

-spec 'prometheus_summary:remove'(name()) -> boolean().
'prometheus_summary:remove'(_) -> error(overlay).

-spec 'prometheus_summary:remove'(name(), label_values()) -> boolean().
'prometheus_summary:remove'(_, _) -> error(overlay).

-spec 'prometheus_summary:remove'(registry(), name(), label_values()) -> boolean().
'prometheus_summary:remove'(_, _, _) -> error(overlay).

-spec 'prometheus_summary:reset'(name()) -> boolean().
'prometheus_summary:reset'(_) -> error(overlay).

-spec 'prometheus_summary:reset'(name(), label_values()) -> boolean().
'prometheus_summary:reset'(_, _) -> error(overlay).

-spec 'prometheus_summary:reset'(registry(), name(), label_values()) -> boolean().
'prometheus_summary:reset'(_, _, _) -> error(overlay).

-spec 'prometheus_summary:value'(name()) -> {Count :: number(), Sum :: number()} | undefined.
'prometheus_summary:value'(_) -> error(overlay).

-spec 'prometheus_summary:value'(name(), label_values()) -> {Count :: number(), Sum :: number()} | undefined.
'prometheus_summary:value'(_, _) -> error(overlay).

%% prometheus_metric:summary_value(); undefined if there is no series for the label values
-spec 'prometheus_summary:value'(registry(), name(), label_values()) ->
          {Count :: number(), Sum :: number()} | undefined.
'prometheus_summary:value'(_, _, _) -> error(overlay).

-spec 'prometheus_summary:values'(registry(), name()) -> [{series_labels(), Count :: number(), Sum :: number()}].
'prometheus_summary:values'(_, _) -> error(overlay).

-spec 'prometheus_summary:deregister_cleanup'(registry()) -> ok.
'prometheus_summary:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_summary:collect_mf'(registry(), prometheus_collector:collect_mf_callback()) -> ok.
'prometheus_summary:collect_mf'(_, _) -> error(overlay).

%% the data is what collect_mf/2 gives to create_mf/5
-spec 'prometheus_summary:collect_metrics'(name(), collect_data_du()) -> [prometheus_model:'Metric'()].
'prometheus_summary:collect_metrics'(_, _) -> error(overlay).

-spec 'prometheus_summary:deregister_select'(registry(), name()) -> ets:match_spec().
'prometheus_summary:deregister_select'(_, _) -> error(overlay).

%% raises invalid_metric_label_name for a label quantile
-spec 'prometheus_summary:validate_summary_spec'(spec()) -> spec().
'prometheus_summary:validate_summary_spec'(_) -> error(overlay).

-spec 'prometheus_summary:validate_summary_labels'([label_name()]) -> [label_name()].
'prometheus_summary:validate_summary_labels'(_) -> error(overlay).

-spec 'prometheus_summary:raise_error_if_quantile_label_found'(label_name()) -> label_name().
'prometheus_summary:raise_error_if_quantile_label_found'(_) -> error(overlay).

%% the fun is called if another process has inserted the series meanwhile
-spec 'prometheus_summary:insert_metric'(registry(), name(), label_values(), Value :: number(),
                                         ConflictCB :: fun((registry(), name(), label_values(), number()) -> ok)) -> ok.
'prometheus_summary:insert_metric'(_, _, _, _, _) -> error(overlay).

%% the rows {Key, Count, ISum, FSum} as [LabelValues, Count, ISum, FSum]
-spec 'prometheus_summary:load_all_values'(registry(), name()) -> [[term()]].
'prometheus_summary:load_all_values'(_, _) -> error(overlay).

-spec 'prometheus_summary:schedulers_seq'() -> [non_neg_integer()].
'prometheus_summary:schedulers_seq'() -> error(overlay).

-spec 'prometheus_summary:key'(registry(), name(), label_values()) -> skey().
'prometheus_summary:key'(_, _, _) -> error(overlay).

%% the rows of the schedulers for one series, each as [Count, ISum, FSum]
-spec 'prometheus_summary:reduce_values'(Values :: [[number()]]) -> {Count :: number(), Sum :: number()}.
'prometheus_summary:reduce_values'(_) -> error(overlay).

-spec 'prometheus_summary:create_summary'(name(), help(), collect_data_du()) -> prometheus_model:'MetricFamily'().
'prometheus_summary:create_summary'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_model_helpers
%% ---------------------------------------------------------------------------------------------

%% "Equivalent to lists:map(fun gauge_metric/1, Values)", and so for the other kinds
-spec 'prometheus_model_helpers:gauge_metrics'([prometheus_model_helpers:gauge()]) -> [prometheus_model:'Metric'()].
'prometheus_model_helpers:gauge_metrics'(_) -> error(overlay).

-spec 'prometheus_model_helpers:untyped_metrics'([prometheus_model_helpers:untyped()]) -> [prometheus_model:'Metric'()].
'prometheus_model_helpers:untyped_metrics'(_) -> error(overlay).

-spec 'prometheus_model_helpers:boolean_metrics'([prometheus_model_helpers:pbool()]) -> [prometheus_model:'Metric'()].
'prometheus_model_helpers:boolean_metrics'(_) -> error(overlay).

-spec 'prometheus_model_helpers:counter_metrics'([prometheus_model_helpers:counter()]) -> [prometheus_model:'Metric'()].
'prometheus_model_helpers:counter_metrics'(_) -> error(overlay).

-spec 'prometheus_model_helpers:summary_metrics'([prometheus_model_helpers:summary()]) -> [prometheus_model:'Metric'()].
'prometheus_model_helpers:summary_metrics'(_) -> error(overlay).

%% "equiv summary_metric([], Count, Sum)"
-spec 'prometheus_model_helpers:summary_metric'(Count :: non_neg_integer(), Sum :: prometheus_model_helpers:value()) ->
          prometheus_model:'Metric'().
'prometheus_model_helpers:summary_metric'(_, _) -> error(overlay).

%% "equiv summary_metric(Labels, Count, Sum, [])"
-spec 'prometheus_model_helpers:summary_metric'(prometheus_model_helpers:labels(), Count :: non_neg_integer(),
                                                Sum :: prometheus_model_helpers:value()) -> prometheus_model:'Metric'().
'prometheus_model_helpers:summary_metric'(_, _, _) -> error(overlay).

-spec 'prometheus_model_helpers:histogram_metrics'([prometheus_model_helpers:histogram()]) ->
          [prometheus_model:'Metric'()].
'prometheus_model_helpers:histogram_metrics'(_) -> error(overlay).

%% "equiv histogram_metric([], Buckets, Count, Sum)"
-spec 'prometheus_model_helpers:histogram_metric'(Buckets :: [{prometheus_buckets:bucket_bound(), non_neg_integer()}],
                                                  Count :: non_neg_integer(),
                                                  Sum :: prometheus_model_helpers:value()) ->
          prometheus_model:'Metric'().
'prometheus_model_helpers:histogram_metric'(_, _, _) -> error(overlay).

%% "Equivalent to lists:map(fun label_pair/1, Labels)"
-spec 'prometheus_model_helpers:label_pairs'(prometheus_model_helpers:labels()) -> [prometheus_model:'LabelPair'()].
'prometheus_model_helpers:label_pairs'(_) -> error(overlay).

%% "Equivalent to lists:map(fun histogram_bucket/1, Specs)"
-spec 'prometheus_model_helpers:histogram_buckets'([{prometheus_buckets:bucket_bound(), non_neg_integer()}]) ->
          [prometheus_model:'Bucket'()].
'prometheus_model_helpers:histogram_buckets'(_) -> error(overlay).

%% type and metrics as create_mf/4 takes them
-spec 'prometheus_model_helpers:metrics_from_tuples'(Type :: mf_type(), [prometheus_model:'Metric'()]
                                                     | prometheus_model:'Metric'()
                                                     | prometheus_model_helpers:metrics()) ->
          [prometheus_model:'Metric'()].
'prometheus_model_helpers:metrics_from_tuples'(_, _) -> error(overlay).

%% the kind of the metric goes with the type: a gauge() for gauge, a pbool() for boolean, ..
-spec 'prometheus_model_helpers:metric_from_tuple'(Type :: mf_type(), prometheus_model:'Metric'()
                                                   | prometheus_model_helpers:tmetric()) ->
          prometheus_model:'Metric'().
'prometheus_model_helpers:metric_from_tuple'(_, _) -> error(overlay).

%% a metric can be undefined: undefined is a value(), and so a gauge(), counter() or untyped()
-spec 'prometheus_model_helpers:filter_undefined_metrics'([prometheus_model:'Metric'()
                                                           | prometheus_model_helpers:tmetric()]) ->
          [prometheus_model:'Metric'() | prometheus_model_helpers:tmetric()].
'prometheus_model_helpers:filter_undefined_metrics'(_) -> error(overlay).

-spec 'prometheus_model_helpers:not_undefined'(term()) -> boolean().
'prometheus_model_helpers:not_undefined'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_protobuf_format
%% ---------------------------------------------------------------------------------------------

%% writes the metrics of a collector to the ram file
-spec 'prometheus_protobuf_format:registry_collect_callback'(file:fd(), registry(),
                                                             prometheus_collector:collector()) -> ok.
'prometheus_protobuf_format:registry_collect_callback'(_, _, _) -> error(overlay).

%% the encoded message with its size in front, as a varint
-spec 'prometheus_protobuf_format:delimited_encode_mf'(prometheus_model:'MetricFamily'()) -> iolist().
'prometheus_protobuf_format:delimited_encode_mf'(_) -> error(overlay).

-spec 'prometheus_protobuf_format:e_varint'(non_neg_integer(), binary()) -> binary().
'prometheus_protobuf_format:e_varint'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_text_format
%% ---------------------------------------------------------------------------------------------

%% writes the metrics of a collector to the ram file
-spec 'prometheus_text_format:registry_collect_callback'(file:fd(), registry(), prometheus_collector:collector()) -> ok.
'prometheus_text_format:registry_collect_callback'(_, _, _) -> error(overlay).

%% the lines # TYPE and # HELP
-spec 'prometheus_text_format:emit_mf_prologue'(file:fd(), prometheus_model:'MetricFamily'()) -> write_ret().
'prometheus_text_format:emit_mf_prologue'(_, _) -> error(overlay).

%% what emit_metric/3 gives for each metric
-spec 'prometheus_text_format:emit_mf_metrics'(file:fd(), prometheus_model:'MetricFamily'()) ->
          [write_ret() | [write_ret()]].
'prometheus_text_format:emit_mf_metrics'(_, _) -> error(overlay).

%% One line for a counter, a gauge and an untyped metric; for a summary and a histogram the lines of
%% count and sum and one for each quantile or bucket. The result is that of the last write, for a
%% summary those of the quantiles
-spec 'prometheus_text_format:emit_metric'(file:fd(), Name :: iodata(), prometheus_model:'Metric'()) ->
          write_ret() | [write_ret()].
'prometheus_text_format:emit_metric'(_, _, _) -> error(overlay).

-spec 'prometheus_text_format:emit_histogram_bucket'(file:fd(), Name :: iodata(), StringLabels :: [iolist()],
                                                     prometheus_model:'Bucket'()) -> write_ret().
'prometheus_text_format:emit_histogram_bucket'(_, _, _, _) -> error(overlay).

%% prometheus_model:'MetricType'()
-spec 'prometheus_text_format:string_type'('COUNTER' | 'GAUGE' | 'SUMMARY' | 'UNTYPED' | 'HISTOGRAM') -> string().
'prometheus_text_format:string_type'(_) -> error(overlay).

%% name="value" for each label
-spec 'prometheus_text_format:labels_stringify'([prometheus_model:'LabelPair'()]) -> [iolist()].
'prometheus_text_format:labels_stringify'(_) -> error(overlay).

%% the labels between braces, with commas
-spec 'prometheus_text_format:labels_string'([iolist()]) -> iolist().
'prometheus_text_format:labels_string'(_) -> error(overlay).

%% the value of a field of 'Counter', 'Gauge', 'Untyped', 'Summary', 'Histogram' or 'Quantile'
-spec 'prometheus_text_format:emit_series'(file:fd(), Name :: iodata(), LString :: iolist(),
                                           Value :: number() | infinity | '-infinity' | nan | undefined) -> write_ret().
'prometheus_text_format:emit_series'(_, _, _, _) -> error(overlay).

-spec 'prometheus_text_format:escape_metric_help'(iodata()) -> binary().
'prometheus_text_format:escape_metric_help'(_) -> error(overlay).

-spec 'prometheus_text_format:escape_help_char'(byte()) -> binary().
'prometheus_text_format:escape_help_char'(_) -> error(overlay).

%% upper_bound of 'Bucket'
-spec 'prometheus_text_format:bound_to_label_value'(number() | infinity) -> string().
'prometheus_text_format:bound_to_label_value'(_) -> error(overlay).

-spec 'prometheus_text_format:escape_label_char'(byte()) -> binary().
'prometheus_text_format:escape_label_char'(_) -> error(overlay).

-spec 'prometheus_text_format:escape_string'(fun((byte()) -> binary()), iodata()) -> binary().
'prometheus_text_format:escape_string'(_, _) -> error(overlay).

-spec 'prometheus_text_format:join_prepend'(Sep :: T, [T]) -> [T].
'prometheus_text_format:join_prepend'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_mnesia_collector
%% ---------------------------------------------------------------------------------------------

%% as collector_metric(), with a fun that gives the metrics: collect_mf/2 calls it under a catch
-type mnesia_metric() :: {Name :: atom(), Type :: mf_type(), help(),
                          DataFun :: fun(() -> prometheus_model_helpers:metrics())}.

-spec 'prometheus_mnesia_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_mnesia_collector:deregister_cleanup'(_) -> error(overlay).

%% what the callback gives
-spec 'prometheus_mnesia_collector:add_metric_family'(mnesia_metric(),
                                                      prometheus_collector:collect_mf_callback()) -> term().
'prometheus_mnesia_collector:add_metric_family'(_, _) -> error(overlay).

-spec 'prometheus_mnesia_collector:metrics'(enabled_metrics()) -> [mnesia_metric()].
'prometheus_mnesia_collector:metrics'(_) -> error(overlay).

%% prometheus_mnesia:tm_info/0 if one of its two metrics is enabled
-spec 'prometheus_mnesia_collector:get_tm_info'(enabled_metrics()) ->
          {Participants :: non_neg_integer(), Coordinators :: non_neg_integer()} | {undefined, undefined}.
'prometheus_mnesia_collector:get_tm_info'(_) -> error(overlay).

-spec 'prometheus_mnesia_collector:tm_metrics_enabled'(enabled_metrics()) -> boolean().
'prometheus_mnesia_collector:tm_metrics_enabled'(_) -> error(overlay).

%% the result of the fun, undefined if it fails
-spec 'prometheus_mnesia_collector:catch_all'(fun(() -> T)) -> T | undefined.
'prometheus_mnesia_collector:catch_all'(_) -> error(overlay).

-spec 'prometheus_mnesia_collector:is_started'(App :: atom()) -> boolean().
'prometheus_mnesia_collector:is_started'(_) -> error(overlay).

-spec 'prometheus_mnesia_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_mnesia_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_mnesia_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_mnesia_collector:metric_enabled'(_, _) -> error(overlay).

%% bytes
-spec 'prometheus_mnesia_collector:get_memory_usage'() -> non_neg_integer().
'prometheus_mnesia_collector:get_memory_usage'() -> error(overlay).

-spec 'prometheus_mnesia_collector:get_tablewise_memory_usage'() -> [{[{table, atom()}], non_neg_integer()}].
'prometheus_mnesia_collector:get_tablewise_memory_usage'() -> error(overlay).

-spec 'prometheus_mnesia_collector:get_tablewise_size'() -> [{[{table, atom()}], non_neg_integer()}].
'prometheus_mnesia_collector:get_tablewise_size'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_vm_dist_collector
%% ---------------------------------------------------------------------------------------------

%% What dist_info/0 collects for a connected node: the process and the state of the connection (of
%% net_kernel:nodes_info/0), the port with its statistics (inet:getstat/1) if the address of the
%% node is known, and the two processes of a connection over TLS
-type dist_node() :: #{dist_pid := pid(), node_state := pending | up_pending | up,
                       inet_stats => [{atom(), integer()}], dist_port => port(),
                       tls_connection_pid => pid(), tls_sender_pid => pid()}.
-type dist_data() :: [{node(), dist_node()}].
-type dist_pid_key() :: dist_pid | tls_connection_pid | tls_sender_pid.

%% the ports with erlang:port_info/1 of each
-type all_ports() :: [{port(), [tuple()] | undefined}].

-spec 'prometheus_vm_dist_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_vm_dist_collector:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:add_metric_family'(collector_metric(),
                                                       prometheus_collector:collect_mf_callback()) -> term().
'prometheus_vm_dist_collector:add_metric_family'(_, _) -> error(overlay).

%% [] if metrics1/0 fails
-spec 'prometheus_vm_dist_collector:metrics'() -> [collector_metric()].
'prometheus_vm_dist_collector:metrics'() -> error(overlay).

-spec 'prometheus_vm_dist_collector:metrics1'() -> [collector_metric()].
'prometheus_vm_dist_collector:metrics1'() -> error(overlay).

-spec 'prometheus_vm_dist_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_vm_dist_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_vm_dist_collector:metric_enabled'(_, _) -> error(overlay).

-spec 'prometheus_vm_dist_collector:dist_info'() -> dist_data().
'prometheus_vm_dist_collector:dist_info'() -> error(overlay).

%% an element of net_kernel:nodes_info/0
-spec 'prometheus_vm_dist_collector:dist_info'({node(), Info :: [{atom(), term()}]}, all_ports()) ->
          {node(), dist_node()}.
'prometheus_vm_dist_collector:dist_info'(_, _) -> error(overlay).

%% SockName is #net_address.address, which has no type in net_address.hrl
-spec 'prometheus_vm_dist_collector:dist_info'(node(), all_ports(), DistPid :: pid(),
                                               NodeState :: pending | up_pending | up, SockName :: term()) ->
          {node(), dist_node()}.
'prometheus_vm_dist_collector:dist_info'(_, _, _, _, _) -> error(overlay).

%% the process connected to the port of the distribution, if it is not the one that owns the connection
-spec 'prometheus_vm_dist_collector:dist_tls_info'(pid()) -> #{tls_connection_pid => pid(), tls_sender_pid => pid()}.
'prometheus_vm_dist_collector:dist_tls_info'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:dist_tls_sender_info'(pid(), #{tls_connection_pid => pid()}) ->
          #{tls_connection_pid => pid(), tls_sender_pid => pid()}.
'prometheus_vm_dist_collector:dist_tls_sender_info'(_, _) -> error(overlay).

%% An item of inet:getstat/1, erlang:port_info/2 or erlang:process_info/2 for each node (for proc
%% of each of the up to three processes); the items that metrics1/0 asks for are integers
-spec 'prometheus_vm_dist_collector:metric'(inet | port | proc, Key :: atom(), dist_data()) -> [{labels(), integer()}].
'prometheus_vm_dist_collector:metric'(_, _, _) -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_proc'(dist_pid_key(), Key :: atom(), dist_data()) -> [{labels(), integer()}].
'prometheus_vm_dist_collector:metric_proc'(_, _, _) -> error(overlay).

-spec 'prometheus_vm_dist_collector:type'(dist_pid_key()) -> dist | tls_connection | tls_sender.
'prometheus_vm_dist_collector:type'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_proc_status'(dist_data()) -> [{labels(), pos_integer()}].
'prometheus_vm_dist_collector:metric_proc_status'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_proc_status'(dist_data(), dist_pid_key()) -> [{labels(), pos_integer()}].
'prometheus_vm_dist_collector:metric_proc_status'(_, _) -> error(overlay).

%% the status of erlang:process_info/2 as a number from 1 to 6
-spec 'prometheus_vm_dist_collector:proc_status'(exiting | suspended | runnable | garbage_collecting | running
                                                 | waiting) -> pos_integer().
'prometheus_vm_dist_collector:proc_status'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_node_state'(dist_data()) -> [{labels(), pos_integer()}].
'prometheus_vm_dist_collector:metric_node_state'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:node_state'(pending | up_pending | up) -> pos_integer().
'prometheus_vm_dist_collector:node_state'(_) -> error(overlay).

-spec 'prometheus_vm_dist_collector:metric_node_queue_size'(dist_data()) -> [{labels(), integer()}].
'prometheus_vm_dist_collector:metric_node_queue_size'(_) -> error(overlay).

%% bytes in the queue of the distribution port; 0 and -1 if erlang:dist_get_stat/1 only says whether it is empty
-spec 'prometheus_vm_dist_collector:node_queue_size'(node()) -> integer().
'prometheus_vm_dist_collector:node_queue_size'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_vm_memory_collector
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_vm_memory_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_vm_memory_collector:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_vm_memory_collector:add_metric_family'(collector_metric(),
                                                         prometheus_collector:collect_mf_callback()) -> term().
'prometheus_vm_memory_collector:add_metric_family'(_, _) -> error(overlay).

-spec 'prometheus_vm_memory_collector:metrics'() -> [collector_metric()].
'prometheus_vm_memory_collector:metrics'() -> error(overlay).

%% what erlang:memory/0 gives
-spec 'prometheus_vm_memory_collector:memory_other'([{atom(), non_neg_integer()}]) -> integer().
'prometheus_vm_memory_collector:memory_other'(_) -> error(overlay).

-spec 'prometheus_vm_memory_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_vm_memory_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_vm_memory_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_vm_memory_collector:metric_enabled'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_vm_msacc_collector
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_vm_msacc_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_vm_msacc_collector:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_vm_msacc_collector:add_metric_family'(collector_metric(),
                                                        prometheus_collector:collect_mf_callback()) -> term().
'prometheus_vm_msacc_collector:add_metric_family'(_, _) -> error(overlay).

-spec 'prometheus_vm_msacc_collector:metrics'() -> [collector_metric()].
'prometheus_vm_msacc_collector:metrics'() -> error(overlay).

%% The seconds of one counter for each thread. Data is what erlang:statistics(microstate_accounting)
%% gives when the accounting is available
-spec 'prometheus_vm_msacc_collector:metric'(Counter :: atom(),
                                             Data :: [#{type := atom(), id := non_neg_integer(),
                                                        counters := #{atom() => non_neg_integer()}}],
                                             SecondAsPerfCounter :: pos_integer()) -> [{labels(), float()}].
'prometheus_vm_msacc_collector:metric'(_, _, _) -> error(overlay).

-spec 'prometheus_vm_msacc_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_vm_msacc_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_vm_msacc_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_vm_msacc_collector:metric_enabled'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_vm_statistics_collector
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_vm_statistics_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_vm_statistics_collector:deregister_cleanup'(_) -> error(overlay).

-spec 'prometheus_vm_statistics_collector:add_metric_family'(collector_metric(),
                                                             prometheus_collector:collect_mf_callback()) -> term().
'prometheus_vm_statistics_collector:add_metric_family'(_, _) -> error(overlay).

-spec 'prometheus_vm_statistics_collector:metrics'() -> [collector_metric()].
'prometheus_vm_statistics_collector:metrics'() -> error(overlay).

%% The lengths of the run queues of the dirty CPU and the dirty IO schedulers: a list of two. The
%% macro recent_otp is not defined in the study, so this is the variant that gives two times undefined
-spec 'prometheus_vm_statistics_collector:dirty_stat'() -> [non_neg_integer() | undefined].
'prometheus_vm_statistics_collector:dirty_stat'() -> error(overlay).

-spec 'prometheus_vm_statistics_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_vm_statistics_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_vm_statistics_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_vm_statistics_collector:metric_enabled'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_vm_system_info_collector
%% ---------------------------------------------------------------------------------------------

-spec 'prometheus_vm_system_info_collector:deregister_cleanup'(registry()) -> ok.
'prometheus_vm_system_info_collector:deregister_cleanup'(_) -> error(overlay).

%% here a metric has no data: collect_metrics/1 gets them by name
-spec 'prometheus_vm_system_info_collector:add_metric_family'({Name :: atom(), Type :: mf_type(), help()},
                                                              prometheus_collector:collect_mf_callback()) -> term().
'prometheus_vm_system_info_collector:add_metric_family'(_, _) -> error(overlay).

-spec 'prometheus_vm_system_info_collector:metrics'() -> [{Name :: atom(), Type :: mf_type(), help()}].
'prometheus_vm_system_info_collector:metrics'() -> error(overlay).

%% The metrics of the allocators, or the item of erlang:system_info/1 with the name of the metric:
%% a number or a boolean; undefined if the item is unknown
-spec 'prometheus_vm_system_info_collector:collect_metrics'(Name :: atom()) ->
          [prometheus_model:'Metric'()] | integer() | boolean() | undefined.
'prometheus_vm_system_info_collector:collect_metrics'(_) -> error(overlay).

-spec 'prometheus_vm_system_info_collector:enabled_metrics'() -> enabled_metrics().
'prometheus_vm_system_info_collector:enabled_metrics'() -> error(overlay).

-spec 'prometheus_vm_system_info_collector:metric_enabled'(Name :: atom(), enabled_metrics()) -> boolean().
'prometheus_vm_system_info_collector:metric_enabled'(_, _) -> error(overlay).

-spec 'prometheus_vm_system_info_collector:collect_allocator_metrics'() -> [prometheus_model:'Metric'()].
'prometheus_vm_system_info_collector:collect_allocator_metrics'() -> error(overlay).

%% carriers or carriers_size of one kind of carriers (mbcs, mbcs_pool, sbcs) of an allocator instance
-spec 'prometheus_vm_system_info_collector:allocator_metric'(Alloc :: atom(), Instance :: non_neg_integer(),
                                                             Kind :: atom(), Key :: atom(), Values :: [tuple()]) ->
          {labels(), non_neg_integer()}.
'prometheus_vm_system_info_collector:allocator_metric'(_, _, _, _, _) -> error(overlay).

%% the instances of the allocators with erlang:system_info({allocator, Alloc}) of each, without the versions
-spec 'prometheus_vm_system_info_collector:allocators'() ->
          [{{Alloc :: atom(), Instance :: non_neg_integer()}, Info :: [{atom(), term()}]}].
'prometheus_vm_system_info_collector:allocators'() -> error(overlay).

%% number or size of the blocks of one kind of carriers
-spec 'prometheus_vm_system_info_collector:allocator_blocks_metric'(Alloc :: atom(), Instance :: non_neg_integer(),
                                                                    Kind :: atom(), count | size,
                                                                    KindInfo :: [tuple()]) ->
          {labels(), non_neg_integer()}.
'prometheus_vm_system_info_collector:allocator_blocks_metric'(_, _, _, _, _) -> error(overlay).

%% the blocks by allocator type, [{Type, [{count, N}, {size, N}]}], as newer versions of OTP give them
-spec 'prometheus_vm_system_info_collector:sum_alloc_block_list'(count | size, [term()], Acc :: non_neg_integer()) ->
          non_neg_integer().
'prometheus_vm_system_info_collector:sum_alloc_block_list'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% prometheus_mnesia, prometheus_test_instrumenter
%% ---------------------------------------------------------------------------------------------

%% the file of a table: its name with the extension, in the directory
-spec 'prometheus_mnesia:table_path'(Dir :: file:name_all(), Table :: file:name(), Ext :: string()) ->
          file:filename_all().
'prometheus_mnesia:table_path'(_, _, _) -> error(overlay).

%% callback of prometheus_instrumenter
-spec 'prometheus_test_instrumenter:setup_instrumenter'() -> ok.
'prometheus_test_instrumenter:setup_instrumenter'() -> error(overlay).
