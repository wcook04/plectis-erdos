#!/usr/bin/env python3
"""Read-only Claude workflow JSONL normalizer; no model calls and no verdicts.
The parser can be reproduced from the public clone without publishing traces.
Do not publish raw prompts, hook contents, commands or answers without review.
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime
import hashlib
import json
from pathlib import Path
from typing import Any

TOKEN_FIELDS = ('input_tokens', 'output_tokens', 'cache_read_input_tokens',
                'cache_creation_input_tokens')

def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                    separators=(',', ':')).encode()).hexdigest()

def read_jsonl(path: Path) -> list[dict]:
    rows = []
    for i, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as e:
            raise ValueError(f'{path.name}:{i}: invalid JSON') from e
        if not isinstance(row, dict):
            raise ValueError(f'{path.name}:{i}: expected an object')
        rows.append(row)
    return rows

def normalize(rows: list[dict]) -> dict:
    """Deduplicate event UUID, message ID and tool ID at their respective levels.

    Usage on split assistant blocks is a repeated/cumulative message total.
    Keep the maximum reported value per message/field; report decreases as an
    anomaly. Never add nested `iterations` to the already aggregated usage.
    Unknown usage/cost is null, never zero. This is one tested schema adapter,
    not a promise about other providers or different usage-accounting schemas.
    """
    events: dict[str, str] = {}
    messages: dict[str, dict] = {}
    unidentified_assistant_events = 0
    tools: dict[str, dict] = {}
    attachments: Counter = Counter()
    attachments_hashes: list[str] = []
    final_objects: dict[str, Any] = {}
    final_attempts: dict[str, Any] = {}
    anomalies: list[str] = []
    times = []
    final_times = []
    models = set()
    for i, row in enumerate(rows):
        uid = row.get('uuid')
        if uid:
            h = digest(row)
            if uid in events:
                if events[uid] != h:
                    raise ValueError('conflicting records share an event UUID')
                continue
            events[uid] = h
        timestamp = row.get('timestamp')
        when = None
        if timestamp:
            try:
                when = datetime.fromisoformat(timestamp.replace('Z', '+00:00'))
                if when.tzinfo is None:
                    raise ValueError('timezone missing')
                times.append(when)
            except (TypeError, ValueError):
                anomalies.append(f'invalid timestamp at event {i + 1}')
        attachment = row.get('attachment', {})
        if row.get('type') == 'attachment' and isinstance(attachment, dict):
            kind = attachment.get('type', 'unknown')
            attachments[kind] += 1
            if kind in ('prompt_snapshot', 'hook_additional_context', 'instructions',
                        'mcp_instructions_delta', 'session_context', 'skill_listing'):
                attachments_hashes.append(digest(attachment))
            if kind == 'structured_output':
                value = attachment.get('data')
                if isinstance(value, dict):
                    final_objects[digest(value)] = value
                    if when:
                        final_times.append(when)
        msg = row.get('message', {})
        if not isinstance(msg, dict) or msg.get('role') != 'assistant':
            continue
        if isinstance(msg.get('model'), str):
            models.add(msg['model'])
        mid = msg.get('id')
        if not mid:
            # Retain content but refuse to invent token totals for unidentified messages.
            unidentified_assistant_events += 1
            anomalies.append(f'assistant message without id at event {i + 1}')
        else:
            acc = messages.setdefault(mid, {f: None for f in TOKEN_FIELDS})
            usage = msg.get('usage')
            if isinstance(usage, dict):
                for field in TOKEN_FIELDS:
                    val = usage.get(field)
                    if val is not None:
                        if type(val) is not int or val < 0:
                            raise ValueError(f'invalid usage field {field}')
                        old = acc[field]
                        if old is not None and val < old:
                            anomalies.append(f'nonmonotone usage: {field}')
                        acc[field] = val if old is None else max(val, old)
        content = msg.get('content', [])
        if not isinstance(content, list):
            continue
        for block in content:
            if not isinstance(block, dict) or block.get('type') != 'tool_use':
                continue
            tid = block.get('id')
            if not tid:
                anomalies.append('tool call without id')
                continue
            normalized = {'name': block.get('name'), 'input': block.get('input')}
            if tid in tools and tools[tid] != normalized:
                raise ValueError('conflicting tool calls share an id')
            tools[tid] = normalized
            if block.get('name') == 'StructuredOutput' and isinstance(block.get('input'), dict):
                value = block['input']
                final_attempts[tid] = value
    usage_output = {}
    for field in TOKEN_FIELDS:
        vals = [m[field] for m in messages.values()]
        known = [v for v in vals if v is not None]
        usage_output[field] = {
            'total_if_complete': sum(known) if vals and len(known) == len(vals)
                                 and not unidentified_assistant_events else None,
            'observed_subtotal': sum(known),
            'messages_missing': len(vals) - len(known) + unidentified_assistant_events}
    end = min(final_times) if final_times else None
    start = min(times) if times else None
    elapsed = (end - start).total_seconds() if start and end else None
    commands = [str(t.get('input', {}).get('command', ''))
                for t in tools.values() if t.get('name') == 'Bash' and isinstance(t.get('input'), dict)]
    query_names = ('query_corpus.py', 'query_continuations.py', 'relation_registry.py', 'research_record.py')
    query_counts = {name: sum(name in c for c in commands) for name in query_names}
    return {
        'schema': 'plectis-reader-trace-analysis/1',
        'boundary': 'observed trace accounting; no mathematical or experimental verdict',
        'raw_rows': len(rows), 'identified_unique_events': len(events),
        'assistant_messages': len(messages), 'models': sorted(models),
        'unidentified_assistant_events': unidentified_assistant_events,
        'tool_counts': dict(sorted(Counter(t['name'] for t in tools.values()).items())),
        'query_command_mentions': query_counts,
        'attachment_counts': dict(sorted(attachments.items())),
        'harness_context_digest': digest(attachments_hashes),
        'usage': usage_output, 'billed_usd': None,
        'elapsed_to_first_accepted_structured_final_seconds': elapsed,
        'structured_output_attempt_count': len(final_attempts),
        'structured_final_count': len(final_objects),
        'structured_final_digests': sorted(final_objects),
        'structured_final': next(iter(final_objects.values())) if len(final_objects) == 1 else None,
        'anomalies': sorted(set(anomalies))}

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('paths', type=Path, nargs='+')
    ap.add_argument('--include-final', action='store_true', help='Private review only; default omits answer text')
    args = ap.parse_args()
    results = []
    for path in args.paths:
        result = normalize(read_jsonl(path))
        result['source_name'] = path.name
        result['source_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        if not args.include_final:
            result.pop('structured_final')
        results.append(result)
    print(json.dumps(results, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
