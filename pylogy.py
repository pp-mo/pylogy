debug = True

class Term(object):
    pass # abstract

#class LiteralTerm(Term):
#    def __init__(self, value):
#        self.value = value
#class VarTerm(Term):
#    def __init__(self, name):
#        self.name = name

class Arg(object):
    def __init__(self, spec):
        self.spec = spec

    @staticmethod
    def spec_is(spec):
        raise ValueError('fails on parent class')

class VarArg(Arg):
    @property
    def name(self):
        return self.spec

    @staticmethod
    def from_spec(spec):
        # A variable spec is a VarArg or an uppercase string.
        if isinstance(spec, VarArg):
            result = spec
        elif isinstance(spec, basestring) and spec[0] == spec[0].upper():
            result = VarArg(spec)
        else:
            result = None
        return result

    def match(self, term):
        result = None
        if isinstance(term, LiteralTerm):
            result = {self: term.value}
#        elif isinstance(term, VarTerm):
#            # We don't match vars to vars (not automatically).
#            pass
        else:
            raise ValueError('unrecognised type of term ?')

        return result

    def __str__(self):
        return '<VarArg "{!s}">'.format(self.name)


class ListConsArg(Arg):
    def __init__(self, head, tail):
        self.head = arg(head)
        self.tail = arg(tail)

    @staticmethod
    def from_spec(spec):
        # A split-list spec is a ListConsArg or a pair.
        if isinstance(spec, VarArg):
            result = spec
        elif isinstance(spec, tuple) and len(spec) == 2:
            result = ListConsArg(*spec)
        else:
            result = None
        return result

    def __str__(self):
        return '<ListConsArg [{!s}|{!s}]>'.format(self.head, self.tail)

    def match(self, term):
        result = None
        if isinstance(term, LiteralTerm):
            value = term.value
            if isinstance(value, list):
                head, tail = value[0], value[1:]
                result = self.head.match(head).update(self.tail.match(tail))
#        elif isinstance(term, VarTerm):
#            # We don't match vars to vars (not automatically).
#            pass
        else:
            raise ValueError('unrecognised type of term ?')

        return result


class LiteralArg(Arg):
    @property
    def value(self):
        return self.spec

    @staticmethod
    def from_spec(spec):
        # A literal spec is anything not a List-splitter or VarArg (for now).
        if isinstance(spec, LiteralArg):
            result = spec
        elif not VarArg.from_spec(spec) and not ListConsArg.from_spec(spec):
            result = LiteralArg(spec)
        else:
            result = None
        return result

    def __str__(self):
        return '<LiteralArg {!r}>'.format(self.value)

    def match(self, term):
        result = None
        if isinstance(term, LiteralTerm):
            if self.value == term.value:
                result = {}
        elif isinstance(term, VarTerm):
            result = {term: self.value}
        else:
            raise ValueError('unrecognised type of term ?')

        return result


class Rule(object):
    def __init__(self, args, terms=None):
        args = args or []
        terms = terms or []
        self.args = [arg(this) for this in args]
        self.terms = [term(this) for this in terms]

    def args_match_context(self, args):
        result = {}
        for arg, given_term in zip(self.args, args):
            match = arg.match(given_term)
            if match is None:
                result = None
                break
            result.update(match)
        return result

    def possibles(self, args=None):
        args_context = self.args_match_context(args)
        if args_context is not None:
            # satisfy rules recursively in turn ...
            for result in self._satisfy_terms(self.terms, args_context):
                yield result

    def _satisfy_terms(self, terms, context):
        if len(terms) == 0:
            # No remaining terms: good to go.
            yield context
        else:
            this_term, rest_terms = terms[0], terms[1:]
            for one_possible in this_term.possibles(context):
                for result in self._satisfy_terms(rest_terms, one_possible):
                    yield result

class Term(object):
    pass

class TrueTerm(Term):
    def possibles(self, context):
        yield context

class FalseTerm(Term):
    def possibles(self, context):
        if 0:
            yield [1]

class ComplexTerm(Term):
    def __init__(self, pred, arg_specs):
        self.pred = pred
        self.arg_specs = [arg(spec) for spec in arg_specs]

    @staticmethod
    def from_spec(spec):
        # A complex term spec is a tuple (pred, args).
        if isinstance(spec, ComplexTerm):
            result = spec
        else:
            result = None
        return result

    def possibles(self, args, context):
        call_context = context.copy()
        match_ok = True
        for arg, arg_spec in zip(args, self.arg_specs):
            match = arg_spec.match(arg)
            if match is None:
                match_ok = False
            else:
                call_context.update(match)
        for result in self.pred.possibles(call_context):
            yield result

class Pred(object):
    def __init__(self, name, rules=None):
        self.name = name
        self.rules = rules or []

    def add(self, rule_args, rule_terms=None):
        # TODO: allow passing existing contructed Rule ?
        self.rules.append(Rule(rule_args, rule_terms))

    def possibles(self, args, context):
        for rule in self.rules:
            for result in rule.possibles(args, context):
                yield result

# Example...
# inlist(X, []) :- !, fail.
# inlist(X, [X|L]).
# inlist(X, [Y|L]) :- inlist(X, L).
# uniq([]).
# uniq([A|L]) :- not inlist(A, L), uniq(L).
#
# ? uniq(1, [2, 1, 3])

class Fail(Pred):
    # Use as Call(Fail, [])
    def __init__(self, args):
        self.args = []

    def add(self, rule):
        raise NotImplementedError()

    def possibles(self, args, context):
        # A generator that stops immediately.
        if 0:
            yield None

class Succeed(Pred):
    # Use as Call(Succeed, [])
    def __init__(self, args):
        self.args = []

    def add(self, rule):
        raise NotImplementedError()

    def possibles(self, args, context):
        # A generator that succeeds once unconditionally.
        yield context


class Not(Pred):
    # A predicate that succeeds once, unconditionally, iff the argument fails.
    def __init__(self, contained_predicate):
        self.pred = contained_predicate

    def possibles(self, args, context):
        inner_succeeded = False
        try:
            # See if there are any possibilities of our argument.
            next(self.pred.possibles(context))
            inner_succeeded = True
        except StopIteration:
            pass
        if not inner_succeeded:
            yield context


def build_from_spec(spec, class_type_name, classes):
    for type in classes:
        result = type.from_spec(spec)
        if result is not None:
            break
    if result is None:
        raise valueError('unexpected {} spec : "{!s}"'.format(
            class_type_name, spec))
    return result

def term(spec):
    return build_from_spec(spec, 'term', [VarArg, ComplexTerm, LiteralArg])

def arg(spec):
    return build_from_spec(spec, 'arg', [VarArg, ListConsArg, LiteralArg])


print arg(1.2)
print arg('xyz')
print arg('Xyz')
print arg(('head', 'Tail'))




# Example...
# inlist(X, []) :- !, fail.
# inlist(X, [X|L]).
# inlist(X, [Y|L]) :- inlist(X, L).
# uniq([]).
# uniq([A|L]) :- not inlist(A, L), uniq(L).
#
# ? uniq([1, 2, 1, 3])

Call = ComplexTerm
Cons = ListConsArg

p_inlist = Pred('inlist')
p_inlist.add(('X', []),
             [Call(Fail, [])])
p_inlist.add(('X', Cons('X', 'L')),
             [])  # or [Call(True, [])]
p_inlist.add(('X', Cons('Y', 'L')),
             [Call(p_inlist, ['X', 'L'])])

p_uniq = Pred('uniq')
p_uniq.add(([]),
           [])
p_uniq.add((Cons('X', 'L')),
           [Not(Call(p_inlist, ['X', 'L'])),
            Call(p_uniq, ['L'])])

debug = True
for result_context in p_uniq.possibles([[1, 2, 1, 3]]):
    print 'result : ', result_context
