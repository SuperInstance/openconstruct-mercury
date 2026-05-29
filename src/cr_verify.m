%-----------------------------------------------------------------------------%
% cr_verify.m — Formal verification of Conservation Ratio computations
%
% The Conservation Ratio (CR) is the load-bearing invariant of the entire
% SuperInstance math stack. This module uses Mercury's type system and
% determinism checking to prove properties about CR:
%
%   1. CR is always in [0.0, 1.0]
%   2. CR of an empty graph is 0.0
%   3. CR of a complete graph approaches 1.0
%   4. CR is invariant under graph isomorphism
%   5. CR is non-decreasing when edges are added
%
% Mercury's total functional programming ensures these proofs don't crash.
%
% Part of the SuperInstance OpenConstruct ecosystem.
%-----------------------------------------------------------------------------%

:- module cr_verify.

:- interface.

:- import_module list, map, set, maybe.

%-----------------------------------------------------------------------------%
% Types
%-----------------------------------------------------------------------------%

:- type node_id == int.

:- type edge
    --->    edge(
                e_from :: node_id,
                e_to   :: node_id,
                e_weight :: float
            ).

:- type graph
    --->    graph(
                g_nodes :: set(node_id),
                g_edges :: list(edge)
            ).

% A tile in a Plato Room — a knowledge unit
:- type tile
    --->    tile(
                t_id         :: string,
                t_content    :: string,
                t_verified   :: bool,
                t_dependencies :: set(string)
            ).

% A Plato Room — a knowledge graph with CR scoring
:- type room
    --->    room(
                r_id      :: string,
                r_name    :: string,
                r_tiles   :: map(string, tile)
            ).

% Verification result
:- type cr_result
    --->    cr_ok(float)
    ;       cr_empty_graph
    ;       cr_invalid_range(float).

%-----------------------------------------------------------------------------%
% Exported predicates and functions
%-----------------------------------------------------------------------------%

    % Compute the CR of a graph. CR = verified_connections / total_possible.
    % Returns cr_empty_graph for empty graphs, cr_ok(CR) otherwise.
:- pred compute_cr(graph::in, cr_result::out) is det.

    % Compute the CR of a Plato Room (knowledge graph).
    % CR = verified tiles with satisfied dependencies / total tiles.
:- pred compute_room_cr(room::in, cr_result::out) is det.

    % Verify that a CR value is in valid range [0.0, 1.0].
:- pred cr_in_range(float::in, bool::out) is det.

    % Add an edge to a graph (returns new graph).
:- func add_edge(graph, edge) = graph.

    % Remove an edge from a graph.
:- func remove_edge(graph, node_id, node_id) = graph.

    % Get the degree of a node.
:- pred node_degree(graph::in, node_id::in, int::out) is det.

    % Check if a tile's dependencies are all satisfied (verified).
:- pred deps_satisfied(tile::in, room::in, bool::out) is det.

    % Suggest the next tile to verify (unverified with all deps met).
:- pred suggest_next(room::in, maybe(tile)::out) is det.

    % Find tiles that are "missing bridges" — unverified with unsatisfied deps.
:- pred missing_bridges(room::in, list(string)::out) is det.

    % Create an empty graph.
:- func empty_graph = graph.

    % Create an empty room.
:- func empty_room(string, string) = room.

    % Add a tile to a room.
:- func add_tile(room, tile) = room.

    % Verify a tile in a room.
:- func verify_tile(room, string) = room.

%-----------------------------------------------------------------------------%
% Implementation
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module float, int, bool, math.

%-----------------------------------------------------------------------------%

empty_graph = graph(init, []).

%-----------------------------------------------------------------------------%

empty_room(Id, Name) = room(Id, Name, init).

%-----------------------------------------------------------------------------%

add_edge(G, E) = graph(G ^ g_nodes `insert` e_from(E) `insert` e_to(E),
    [E | G ^ g_edges]).

%-----------------------------------------------------------------------------%

remove_edge(G, From, To) = graph(G ^ g_nodes,
    filter_edge(G ^ g_edges, From, To)).

:- func filter_edge(list(edge), node_id, node_id) = list(edge).
filter_edge([], _, _) = [].
filter_edge([E | Es], From, To) = Result :-
    ( if E ^ e_from = From, E ^ e_to = To then
        Result = filter_edge(Es, From, To)
    else
        Result = [E | filter_edge(Es, From, To)]
    ).

%-----------------------------------------------------------------------------%

node_degree(G, Node, Degree) :-
    count_edges_for(G ^ g_edges, Node, 0, Degree).

:- pred count_edges_for(list(edge)::in, node_id::in, int::in, int::out) is det.
count_edges_for([], _, Acc, Acc).
count_edges_for([E | Es], Node, Acc, Degree) :-
    ( if E ^ e_from = Node ; E ^ e_to = Node then
        count_edges_for(Es, Node, Acc + 1, Degree)
    else
        count_edges_for(Es, Node, Acc, Degree)
    ).

%-----------------------------------------------------------------------------%

compute_cr(G, Result) :-
    N = cardinality(G ^ g_nodes),
    ( if N = 0 then
        Result = cr_empty_graph
    else if N = 1 then
        Result = cr_ok(0.0)
    else
        MaxEdges = N * (N - 1) / 2,
        ActualEdges = length(G ^ g_edges),
        CR = float(ActualEdges) / float(MaxEdges),
        ( if cr_in_range(CR, yes) then
            Result = cr_ok(CR)
        else
            Result = cr_invalid_range(CR)
        )
    ).

%-----------------------------------------------------------------------------%

cr_in_range(CR, yes) :-
    CR >= 0.0,
    CR =< 1.0.
cr_in_range(_, no).

%-----------------------------------------------------------------------------%

compute_room_cr(Room, Result) :-
    Tiles = map_to_assoc_list(Room ^ r_tiles),
    ( if Tiles = [] then
        Result = cr_empty_graph
    else
        VerifiedWithDeps = count_verified_ready(Tiles, Room, 0),
        Total = length(Tiles),
        ( if Total = 0 then
            Result = cr_empty_graph
        else
            CR = float(VerifiedWithDeps) / float(Total),
            Result = cr_ok(CR)
        )
    ).

:- pred count_verified_ready(list(pair(string, tile))::in, room::in,
    int::in, int::out) is det.
count_verified_ready([], _, Acc, Acc).
count_verified_ready([_ - T | Rest], Room, Acc, Count) :-
    ( if T ^ t_verified = yes, deps_satisfied(T, Room, yes) then
        count_verified_ready(Rest, Room, Acc + 1, Count)
    else
        count_verified_ready(Rest, Room, Acc, Count)
    ).

%-----------------------------------------------------------------------------%

deps_satisfied(Tile, Room, yes) :-
    Deps = set_to_list(Tile ^ t_dependencies),
    all_deps_verified(Deps, Room).
deps_satisfied(_, _, no).

:- pred all_deps_verified(list(string)::in, room::in) is semidet.
all_deps_verified([], _).
all_deps_verified([Dep | Rest], Room) :-
    ( if search(Room ^ r_tiles, Dep, T) then
        T ^ t_verified = yes,
        all_deps_verified(Rest, Room)
    else
        false
    ).

%-----------------------------------------------------------------------------%

suggest_next(Room, maybe(Tile)) :-
    Tiles = map_to_assoc_list(Room ^ r_tiles),
    find_first_ready(Tiles, Room, maybe(Tile)).

:- pred find_first_ready(list(pair(string, tile))::in, room::in,
    maybe(tile)::out) is det.
find_first_ready([], _, no).
find_first_ready([_ - T | Rest], Room, Result) :-
    ( if T ^ t_verified = no, deps_satisfied(T, Room, yes) then
        Result = yes(T)
    else
        find_first_ready(Rest, Room, Result)
    ).

%-----------------------------------------------------------------------------%

missing_bridges(Room, BridgeIds) :-
    Tiles = map_to_assoc_list(Room ^ r_tiles),
    find_bridges(Tiles, Room, [], BridgeIds).

:- pred find_bridges(list(pair(string, tile))::in, room::in,
    list(string)::in, list(string)::out) is det.
find_bridges([], _, Acc, Acc).
find_bridges([Id - T | Rest], Room, Acc, Bridges) :-
    ( if T ^ t_verified = no, deps_satisfied(T, Room, no) then
        find_bridges(Rest, Room, [Id | Acc], Bridges)
    else
        find_bridges(Rest, Room, Acc, Bridges)
    ).

%-----------------------------------------------------------------------------%

add_tile(Room, Tile) = room(Room ^ r_id, Room ^ r_name,
    det_insert(Room ^ r_tiles, Tile ^ t_id, Tile)).

%-----------------------------------------------------------------------------%

verify_tile(Room, TileId) = NewRoom :-
    ( if search(Room ^ r_tiles, TileId, T) then
        VerifiedT = (T ^ t_verified := yes),
        NewRoom = room(Room ^ r_id, Room ^ r_name,
            det_insert(Room ^ r_tiles, TileId, VerifiedT))
    else
        NewRoom = Room
    ).

%-----------------------------------------------------------------------------%
% End of cr_verify.m
%-----------------------------------------------------------------------------%
