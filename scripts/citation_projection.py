#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""CFF reference projection owned by the scholarly source registry."""
from __future__ import annotations
import json
from urllib.parse import quote

ATTRIBUTION_PREFIX = 'https://github.com/wcook04/plectis-erdos/blob/main/docs/research-commons/SOURCE_ATTRIBUTIONS.md#source-'
PAPER_PREFIX = 'https://github.com/wcook04/plectis-erdos/blob/main/docs/papers/full-text/'

def reference_id(reference):
    paper_ids = [i['value'] for i in reference.get('identifiers', []) if i.get('type') == 'other' and i.get('value','').startswith('paper:')]
    if paper_ids:
        if len(paper_ids) != 1: raise ValueError('duplicate paper identity')
        return paper_ids[0]
    anchors = [i['value'] for i in reference.get('identifiers', []) if i.get('type') == 'url' and (i.get('value','').startswith(ATTRIBUTION_PREFIX) or i.get('value','').startswith(PAPER_PREFIX))]
    if not anchors or len(set(anchors)) != len(anchors) or (any(a.startswith(PAPER_PREFIX) for a in anchors) and len(anchors) != 1):
        raise ValueError('reference requires source identity anchors or exactly one paper identity anchor')
    anchor = anchors[0]
    return ('source:' + anchor[len(ATTRIBUTION_PREFIX):]) if anchor.startswith(ATTRIBUTION_PREFIX) else ('paper:' + anchor[len(PAPER_PREFIX):-3])

def coverage(index):
    sources = {s['id']: s for s in index['sources']}
    errors = []
    if not sources:
        errors.append('source registry must not be empty')
    for source in sources.values():
        choices=sum(bool(source.get(field)) for field in ('citation','citation_alias','citation_exclusion'))
        if choices != 1:
            errors.append(f"source {source['id']}: exactly one citation, alias or explicit exclusion required")
        if source.get('citation_alias') and not sources.get(source['citation_alias'],{}).get('citation'):
            errors.append(f"source {source['id']}: invalid citation alias")
    for row in index['paper_inventory']['bibliography_entries']:
        source = sources.get(row.get('explicit_source_id'))
        if source is None:
            errors.append(f"unrepresented bibliography {row['path']}:{row['key']}")
        elif not source.get('citation') and not source.get('citation_exclusion') and not sources.get(source.get('citation_alias'),{}).get('citation'):
            errors.append(f"missing citation metadata {source['id']} for {row['path']}:{row['key']}")
    for row in index['paper_inventory']['unmatched_citation_keys']:
        errors.append(f"undefined bibliography {row['paper_id']}:{row['key']}")
    for row in index['paper_inventory']['unresolved_includes']:
        errors.append(f"unresolved manuscript include {row}")
    return errors

def references(index, corpus, root=None):
    errors = coverage(index)
    if errors:
        raise ValueError('; '.join(errors))
    result = []
    for source in sorted(index['sources'], key=lambda s:s['id']):
        if not source.get('citation'):
            continue
        metadata = json.loads(json.dumps(source['citation']))
        ref = {'type':metadata.pop('type'), **metadata}
        ref['identifiers'] = [item for item in ref.get('identifiers',[]) if not (item.get('type') == 'url' and item.get('value','').startswith(ATTRIBUTION_PREFIX))]
        aliases = sorted(s['id'] for s in index['sources'] if s.get('citation_alias') == source['id'])
        for source_id in [source['id'], *aliases]:
            ref.setdefault('identifiers', []).append({'type':'url','value':ATTRIBUTION_PREFIX + source_id, 'description':'Source attribution and exact local uses'})
        result.append(ref)
    for paper in sorted(corpus['papers'], key=lambda p:p['paper_id']):
        if root is not None:
            for field in ('local_source','local_full_text'):
                if not (root / paper[field]).is_file():
                    raise ValueError(f"paper {paper['paper_id']}: missing {field} {paper[field]}")
        preferred = paper['preferred_citation']
        author = preferred['author']
        ref = {'type':'report','title':preferred['title'],'authors':[{'family-names':'Cook','given-names':'Will'}] if author == 'Will Cook' else [{'name':author}], 'year':int(preferred['year']), 'url':preferred.get('canonical_source_url') or 'https://github.com/wcook04/plectis-erdos/blob/main/' + quote(paper['local_source']), 'notes':f"Repository manuscript; status: {paper['manuscript_status']}; publication state: {paper.get('publication_state','unspecified')}. {preferred['text']}", 'identifiers':[{'type':'other','value':'paper:'+paper['paper_id'],'description':'Repository paper edition'}, {'type':'url','value':'https://github.com/wcook04/plectis-erdos/blob/main/'+quote(paper['local_full_text']),'description':'Searchable paper text'}]}
        if paper.get('doi'): ref['doi'] = paper['doi']
        # Merge only the same authored edition: exact primary URL, title and
        # author identity. Identically titled compact/detailed papers stay separate.
        def author_names(reference):
            return [a.get('name') or ' '.join(filter(None,(a.get('given-names'),a.get('family-names')))) for a in reference.get('authors',[])]
        matching=[old for old in result if reference_id(old).startswith('source:') and old.get('url') == ref['url'] and old.get('title') == ref['title'] and author_names(old) == author_names(ref)]
        for old in matching:
            ref['identifiers'].extend(old.get('identifiers',[]))
            result.remove(old)
        ref['identifiers']=[dict(item) for item in {json.dumps(item,sort_keys=True):item for item in ref['identifiers']}.values()]
        result.append(ref)
    ids = [reference_id(r) for r in result]
    if not result or len(set(ids)) != len(ids):
        raise ValueError('empty references or duplicate reference identities')
    return result

def yaml_lines(value, indent=0):
    pad = ' ' * indent
    if isinstance(value, dict):
        for key, item in value.items():
            if isinstance(item, (dict,list)) and item:
                yield pad + key + ':'
                yield from yaml_lines(item, indent + 2)
            else:
                yield pad + key + ': ' + json.dumps(item, ensure_ascii=False)
    elif isinstance(value,list):
        for item in value:
            if isinstance(item,(dict,list)) and item:
                lines = list(yaml_lines(item, indent + 2))
                yield pad + '- ' + lines[0][indent+2:]
                yield from lines[1:]
            else:
                yield pad + '- ' + json.dumps(item, ensure_ascii=False)

def render(cff, refs):
    header = cff.split('\nreferences:\n',1)[0].rstrip()
    return header + '\nreferences:\n' + '\n'.join(yaml_lines(refs,2)) + '\n'

def errors(cff, index, corpus):
    expected = render(cff, references(index, corpus))
    return [] if cff == expected else ['CITATION.cff references are missing, duplicated, misidentified, or stale; run scripts/build_source_attributions.py']
