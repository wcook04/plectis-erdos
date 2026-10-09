<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Prompts for working from an agent trace

These are public adaptations of Will Cook's Continue Intelligently, Semantic
Carryforward and Context Compaction prompts used in the
[Agent Trace demonstration](https://youtu.be/SGeVUNqjfsk). They retain the original
purposes without the private workspace's paths, routing rules or parser contract.

The workflow is simple: an agent works on a project, you give its trace and any
needed source material to another model, and you bring the resulting answer
back to the agent. In these prompts, **Type A** is the agent that can inspect and
change the project; **Type B** is the model reasoning from the supplied evidence.
The distinction is about access and responsibility, not intelligence or provider.

| Prompt | Use it to |
| --- | --- |
| [Continue Intelligently](continue-intelligently.md) | Reconcile a new trace with the receiving conversation and develop the reasoning that should guide the next pass. |
| [Semantic Carry Forward](semantic-carry-forward.md) | Push an existing direction further through a better abstraction, research, design or experiment. A new paste is optional. |
| [Context Compaction](context-compaction.md) | Preserve source state in a restart packet without adding recommendations. |

Copy the text inside the chosen prompt's code block. For continuation, paste or
attach the trace in the receiving conversation, add relevant files or excerpts,
and state any correction or desired direction. Return the model's answer to the
working agent so it can compare the advice with the actual project. For
compaction, specify which conversation or artifact is the source. Use one of the
continuation prompts afterward if you want new reasoning.

A trace supplies recorded context, not access to the original workspace. A
referenced file is readable only if its contents are supplied or an available
tool can retrieve it. In the filmed comparison, Codex could read the local
repository; ChatGPT received a selected ZIP packet and the pasted thread trace.

A restart packet can omit detail. Retain the original when exact wording or
tool output matters. These prompts guide work; they do not validate results or
replace the working project's instructions. The repository's
[agent guide](../AGENT_GUIDE.md) governs contributions here.
