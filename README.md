# Formalizing a subset of GodotScript
A project for EPFL Interactive Theorem Proving course (CS-428).

This project formalizes a subset of GDScript, the scripting language of the Godot game engine, using the Rocq proof assistant, with a focus on its event-driven signal system (awaiting and emitting signals). \
We define big-step semantics for single-node and dual-node (two interacting nodes) execution, including context switching for cross-node signal callbacks, and validate the semantics by proving correct behavior on a set of example programs translated from Godot. \
Current limitations include support for only two classes, unique signal names across nodes, and no binding statements for signal-callback connections.

Check out [report.pdf](report.pdf) for the full write-up, including our design decisions, limitations, and ideas for future work.
