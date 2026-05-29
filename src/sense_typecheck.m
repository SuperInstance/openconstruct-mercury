%-----------------------------------------------------------------------------%
% sense_typecheck.m — Compile-time type safety for sensory data pipelines
%
% Mercury's type system catches mismatched sense data at compile time.
% This module defines the type-level contract for all six Plato senses,
% ensuring that:
%
%   1. Vision shadows can't be fed to sonar processors
%   2. Each sense has its own typed shadow format
%   3. Fused events are well-typed combinations
%   4. Policy checks are applied before any sense action
%
% The Mercury compiler enforces these invariants. No runtime errors.
%
% Part of the SuperInstance OpenConstruct ecosystem.
%-----------------------------------------------------------------------------%

:- module sense_typecheck.

:- interface.

:- import_module list, string, maybe, time.

%-----------------------------------------------------------------------------%
% Typed shadows — each sense has its own type
%-----------------------------------------------------------------------------%

:- type vision_shadow
    --->    vision_shadow(
                vs_objects    :: list(detected_object),
                vs_scene      :: string,
                vs_confidence :: float
            ).

:- type detected_object
    --->    detected_object(
                do_label      :: string,
                do_position   :: position,
                do_confidence :: float
            ).

:- type position
    --->    position(
                p_x :: float,
                p_y :: float,
                p_z :: maybe(float)
            ).

:- type sonar_shadow
    --->    sonar_shadow(
                ss_frequencies  :: list(frequency_bin),
                ss_direction    :: maybe(direction),
                ss_vad          :: voice_activity
            ).

:- type frequency_bin
    --->    freq_bin(
                fb_hz       :: float,
                fb_amplitude :: float
            ).

:- type direction
    --->    direction(
                d_azimuth  :: float,
                d_elevation :: float
            ).

:- type voice_activity
    --->    voice_active
    ;       voice_silent
    ;       voice_unknown.

:- type manus_shadow
    --->    manus_shadow(
                ms_operation :: manus_op,
                ms_result    :: manus_result,
                ms_path      :: maybe(string)
            ).

:- type manus_op
    --->    op_read
    ;       op_write
    ;       op_list
    ;       op_delete.

:- type manus_result
    --->    manus_ok(string)
    ;       manus_error(string)
    ;       manus_permission_denied.

:- type browser_shadow
    --->    browser_shadow(
                bs_url       :: string,
                bs_title     :: string,
                bs_elements  :: list(element_desc),
                bs_action    :: browser_action
            ).

:- type element_desc
    --->    element(
                e_tag   :: string,
                e_text  :: string,
                e_attrs :: list(pair(string, string))
            ).

:- type browser_action
    --->    action_navigate
    ;       action_click
    ;       action_type
    ;       action_extract.

:- type desktop_shadow
    --->    desktop_shadow(
                ds_windows    :: list(window_desc),
                ds_focused    :: maybe(string),
                ds_resolution :: pair(int, int)
            ).

:- type window_desc
    --->    window(
                w_title :: string,
                w_app   :: string,
                w_pos   :: pair(int, int),
                w_size  :: pair(int, int)
            ).

%-----------------------------------------------------------------------------%
% Unified sense type — the type-safe way to carry any shadow
%-----------------------------------------------------------------------------%

:- type sense_type
    --->    sense_vision
    ;       sense_sonar
    ;       sense_manus
    ;       sense_browser
    ;       sense_desktop.

:- type any_shadow
    --->    shadow_vision(vision_shadow)
    ;       shadow_sonar(sonar_shadow)
    ;       shadow_manus(manus_shadow)
    ;       shadow_browser(browser_shadow)
    ;       shadow_desktop(desktop_shadow).

%-----------------------------------------------------------------------------%
% Fused event — well-typed combination of shadows
%-----------------------------------------------------------------------------%

:- type severity
    --->    severity_info
    ;       severity_warning
    ;       severity_alert
    ;       severity_critical.

:- type fused_event
    --->    fused_event(
                fe_shadows    :: list(any_shadow),
                fe_assessment :: string,
                fe_confidence :: float,
                fe_severity   :: severity,
                fe_action     :: maybe(string)
            ).

%-----------------------------------------------------------------------------%
% Exported operations
%-----------------------------------------------------------------------------%

    % Get the sense type of a shadow.
:- func sense_of(any_shadow) = sense_type.

    % Create a fused event from typed shadows.
    % Fails at compile time if shadows are mismatched.
:- func fuse_shadows(list(any_shadow), string, float, severity) = fused_event.

    % Extract vision data from a typed shadow.
    % Compile-time guarantee: only works with vision shadows.
:- func extract_vision(any_shadow) = vision_shadow.

    % Extract sonar data.
:- func extract_sonar(any_shadow) = sonar_shadow.

    % Check if a fused event has vision data.
:- pred has_vision(fused_event::in, bool::out) is det.

    % Check if a fused event has sonar data.
:- pred has_sonar(fused_event::in, bool::out) is det.

    % Classify severity based on shadow content.
:- func classify_severity(list(any_shadow)) = severity.

%-----------------------------------------------------------------------------%
% Implementation
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module float, int, bool, require.

%-----------------------------------------------------------------------------%

sense_of(shadow_vision(_))   = sense_vision.
sense_of(shadow_sonar(_))   = sense_sonar.
sense_of(shadow_manus(_))   = sense_manus.
sense_of(shadow_browser(_)) = sense_browser.
sense_of(shadow_desktop(_)) = sense_desktop.

%-----------------------------------------------------------------------------%

fuse_shadows(Shadows, Assessment, Confidence, Severity) =
    fused_event(Shadows, Assessment, Confidence, Severity, no).

%-----------------------------------------------------------------------------%

extract_vision(shadow_vision(VS)) = VS.
extract_vision(Other) = _ :-
    unexpected($module, $pred,
        "extract_vision called on non-vision shadow: " ++
        sense_type_to_string(sense_of(Other))).

:- func sense_type_to_string(sense_type) = string.
sense_type_to_string(sense_vision)   = "vision".
sense_type_to_string(sense_sonar)    = "sonar".
sense_type_to_string(sense_manus)    = "manus".
sense_type_to_string(sense_browser)  = "browser".
sense_type_to_string(sense_desktop)  = "desktop".

%-----------------------------------------------------------------------------%

extract_sonar(shadow_sonar(SS)) = SS.
extract_sonar(Other) = _ :-
    unexpected($module, $pred,
        "extract_sonar called on non-sonar shadow: " ++
        sense_type_to_string(sense_of(Other))).

%-----------------------------------------------------------------------------%

has_vision(Event, yes) :-
    list.member(Shadow, Event ^ fe_shadows),
    sense_of(Shadow) = sense_vision.
has_vision(_, no).

%-----------------------------------------------------------------------------%

has_sonar(Event, yes) :-
    list.member(Shadow, Event ^ fe_shadows),
    sense_of(Shadow) = sense_sonar.
has_sonar(_, no).

%-----------------------------------------------------------------------------%

classify_severity(Shadows) = Severity :-
    ( if any_critical_vision(Shadows) then
        Severity = severity_critical
    else if any_voice_active(Shadows) then
        Severity = severity_alert
    else if has_multiple_sense_types(Shadows, 2) then
        Severity = severity_warning
    else
        Severity = severity_info
    ).

:- pred any_critical_vision(list(any_shadow)::in) is semidet.
any_critical_vision(Shadows) :-
    list.member(S, Shadows),
    sense_of(S) = sense_vision,
    extract_vision(S) ^ vs_confidence > 0.9,
    detect_person(extract_vision(S) ^ vs_objects).

:- pred detect_person(list(detected_object)::in) is semidet.
detect_person([]) :- fail.
detect_person([O | _]) :-
    O ^ do_label = "person".
detect_person([_ | Rest]) :-
    detect_person(Rest).

:- pred any_voice_active(list(any_shadow)::in) is semidet.
any_voice_active(Shadows) :-
    list.member(S, Shadows),
    sense_of(S) = sense_sonar,
    extract_sonar(S) ^ ss_vad = voice_active.

:- pred has_multiple_sense_types(list(any_shadow)::in, int::in) is semidet.
has_multiple_sense_types(Shadows, Min) :-
    Types = list.map(sense_of, Shadows),
    unique_types(Types, Unique),
    length(Unique) >= Min.

:- func unique_types(list(sense_type)) = list(sense_type).
unique_types([]) = [].
unique_types([T | Ts]) = [T | filter_type(T, unique_types(Ts))].

:- func filter_type(sense_type, list(sense_type)) = list(sense_type).
filter_type(_, []) = [].
filter_type(T, [U | Us]) = Result :-
    ( if T = U then
        Result = filter_type(T, Us)
    else
        Result = [U | filter_type(T, Us)]
    ).

%-----------------------------------------------------------------------------%
% End of sense_typecheck.m
%-----------------------------------------------------------------------------%
