# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
import ast
import unittest
import sympy as sp
from search import arithmetic, solve, VARS

class ConstructionSearchTests(unittest.TestCase):
    def test_arithmetic_reader_rejects_executable_python(self):
        for expression in ('__import__("os")', 'a.real', 'a[0]', 'a / D', 'a ** -1'):
            with self.assertRaises(ValueError):
                arithmetic(ast.parse(expression, mode='eval'), dict(zip(('a','D','C'), VARS)))

    def test_no_given_coordinate_needed_and_changed_dynamics_do_not_reuse_it(self):
        a,D,C=VARS
        found=solve([a*a-a+1,a*D,a*C-D])
        mixed=[row for row in found if C in row['expr'].free_symbols]
        self.assertEqual(len(mixed),1)
        f=mixed[0]['expr']
        self.assertEqual(sp.expand(f.subs({a:a*a-a+1,D:a*D,C:a*C-D}, simultaneous=True)-a*a*f),0)
        self.assertNotEqual(sp.expand(f.subs({a:a*a-a,D:a*D,C:a*C-D}, simultaneous=True)-a*a*f),0)
        altered=solve([a*a-a,a*D,a*C-D])
        self.assertFalse(any(C in row['expr'].free_symbols for row in altered))

if __name__=='__main__': unittest.main()
