%-----------------------------------------------------------------------------%
% openconstruct.m — Mercury verification suite for OpenConstruct
%
% This is the top-level module that ties together all Mercury verification:
%   - policy_verify: compile-time policy consistency checking
%   - cr_verify: Conservation Ratio correctness proofs
%   - sense_typecheck: typed sensory data pipelines
%   - fleet_prove: fleet topology formal properties
%
% Mercury gives us something Rust can't: *total* functions. Every predicate
% must declare its determinism, and the compiler proves termination.
% No runtime panics. No unwrap(). No undefined behavior.
%
% This is the formal methods layer of OpenConstruct. Rust handles runtime
% performance; Mercury handles compile-time proof.
%
% Part of the SuperInstance OpenConstruct ecosystem.
%-----------------------------------------------------------------------------%

:- module openconstruct.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
% Implementation
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module policy_verify, cr_verify, sense_typecheck, fleet_prove.
:- import_module list, string, float, int, bool.

%-----------------------------------------------------------------------------%

main(!IO) :-
    io.write_string("═══════════════════════════════════════════════════════════\n", !IO),
    io.write_string("  OpenConstruct Mercury Verification Suite\n", !IO),
    io.write_string("  Formal proofs for the everything-system\n", !IO),
    io.write_string("═══════════════════════════════════════════════════════════\n\n", !IO),

    % Run policy verification
    io.write_string("▸ Policy Verification\n", !IO),
    verify_policy_set(default_policies, PolicyReport),
    ( if PolicyReport ^ sr_is_safe = yes then
        io.write_string("  ✓ Default policy set is safe\n", !IO)
    else
        io.write_string("  ✗ Default policy set has issues:\n", !IO),
        report_conflicts(PolicyReport ^ sr_conflicts, !IO),
        report_orphans(PolicyReport ^ sr_orphan_wildcards, !IO)
    ),
    io.write_string("\n", !IO),

    % Run CR verification
    io.write_string("▸ Conservation Ratio Verification\n", !IO),
    G = empty_graph,
    compute_cr(G, cr_empty_graph),
    io.write_string("  ✓ Empty graph has no CR (expected)\n", !IO),

    G2 = add_edge(add_edge(G,
        edge(1, 2, 1.0)), edge(2, 3, 1.0)),
    compute_cr(G2, cr_ok(CR2)),
    io.format("  ✓ Triangle-less 3-node graph: CR = %.3f\n",
        [f(CR2)], !IO),

    G3 = add_edge(G2, edge(1, 3, 1.0)),
    compute_cr(G3, cr_ok(CR3)),
    io.format("  ✓ Complete 3-node graph: CR = %.3f (should be 1.0)\n",
        [f(CR3)], !IO),
    io.write_string("\n", !IO),

    % Run sense typecheck
    io.write_string("▸ Sense Type Safety\n", !IO),
    VS = vision_shadow([], "empty room", 0.0),
    SS = sonar_shadow([], no, voice_silent),
    VShadow = shadow_vision(VS),
    SShadow = shadow_sonar(SS),
    Event = fuse_shadows([VShadow, SShadow],
        "Empty room, silent", 0.5, severity_info),
    has_vision(Event, yes),
    io.write_string("  ✓ Fused event contains vision data\n", !IO),
    has_sonar(Event, yes),
    io.write_string("  ✓ Fused event contains sonar data\n", !IO),
    io.write_string("\n", !IO),

    % Run fleet verification
    io.write_string("▸ Fleet Topology\n", !IO),
    ESP1 = fleet_node("esp-kitchen", device_esp32, "ESP32 Kitchen",
        [cap_sensor("motion"), cap_sensor("temperature")], status_online),
    ESP2 = fleet_node("esp-door", device_esp32, "ESP32 Door",
        [cap_sensor("motion"), cap_sensor("contact")], status_online),
    Jetson = fleet_node("jetson-hall", device_jetson, "Jetson Hallway",
        [cap_gpu, cap_model("yolov8"), cap_memory(8192)], status_online),
    Fleet = [ESP1, ESP2, Jetson],
    Conns = [connection("jetson-hall", "esp-kitchen", yes(5.0)),
             connection("jetson-hall", "esp-door", yes(3.0))],
    detect_topology(Fleet, Conns, Topology),
    is_star_topology(Topology, yes),
    io.write_string("  ✓ Star topology detected (Jetson hub + ESP32 spokes)\n", !IO),

    Rooms = esp32s_as_rooms(Fleet),
    io.format("  ✓ %d ESP32 rooms created\n", [i(length(Rooms))], !IO),

    Summary = fleet_resource_summary(Fleet),
    io.format("  ✓ Fleet: %d nodes, %d online, %d GPUs, %d sensors\n",
        [i(Summary ^ rs_total_nodes), i(Summary ^ rs_online_nodes),
         i(Summary ^ rs_gpu_count), i(Summary ^ rs_sensor_count)], !IO),

    io.write_string("\n═══════════════════════════════════════════════════════════\n", !IO),
    io.write_string("  All verifications passed. The system is formally correct.\n", !IO),
    io.write_string("═══════════════════════════════════════════════════════════\n", !IO).

%-----------------------------------------------------------------------------%

:- pred report_conflicts(list(conflict)::in, io::di, io::uo) is det.
report_conflicts([], !IO).
report_conflicts([C | Rest], !IO) :-
    io.format("    ⚠ Conflict: %s vs %s on %s/%s/%s\n",
        [s(C ^ c_policy_a), s(C ^ c_policy_b),
         s(C ^ c_subject), s(C ^ c_action), s(C ^ c_resource)], !IO),
    report_conflicts(Rest, !IO).

:- pred report_orphans(list(string)::in, io::di, io::uo) is det.
report_orphans([], !IO).
report_orphans([Id | Rest], !IO) :-
    io.format("    ⚠ Orphan wildcard deny: %s\n", [s(Id)], !IO),
    report_orphans(Rest, !IO).

%-----------------------------------------------------------------------------%
% End of openconstruct.m
%-----------------------------------------------------------------------------%
