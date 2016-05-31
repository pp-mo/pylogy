debug = True

def db(ind, str):
    if debug:
        print ' ' * ind + str

class ArgOrTerm(object):
    @classmethod
    def from_spec(cls, spec):
        # Pass-through object of this class, or build from a suitable spec.
        if isinstance(spec, cls):
            result = spec
        elif cls.is_valid_spec(spec):
            result = cls(spec)
        else:
            result = None
        return result

    @classmethod
    def is_valid_spec(cls, spec):
        raise NotImplementedError()

    def final_value(self):
        # Result chaining for variable contents and equivalences.
        return self

    def __repr__(self):
        return str(self)

    def __str__(self):
        part_strs = ['{}={!r}'.format(
                         part, getattr(self, part))
                     for part in self.parts]
        parts_str = ', '.join(part_strs)
        if len(parts_str) > 0:
            parts_str = ' ' + parts_str
        name = self.__class__.__name__
        return '<{}{}>'.format(name, parts_str)


class Arg(ArgOrTerm):
    def __init__(self, spec):
        self.spec = spec

    def match_term(self, term, caller_vars, local_vars):
        # Match a formal arg to a call argument term, updating dictionaries of
        # local vars and caller vars.
        raise NotImplementedError()


class VarArg(Arg):
    parts = ('name', 'value')

    def __init__(self, spec, value=None):
        super(VarArg, self).__init__(spec)
        self.value = value

    @property
    def name(self):
        return self.spec

    @classmethod
    def is_valid_spec(cls, spec):
        # A Var is denoted by any string with leading uppercase.
        return isinstance(spec, basestring) and spec[0] == spec[0].upper()

    def final_value(self):
        if self.value is None:
            result = self
        else:
            result = self.value.final_value()
        return result

    argvar_number = 0

    @classmethod
    def _new_var(cls, name):
        cls.argvar_number += 1
        var = VarTerm('{}_{:03d}'.format(name, cls.argvar_number))
        return var

    def match_term(self, term, caller_vars, local_vars):
        result = True
        if self.name in local_vars:
            var = local_vars[self.name]
        else:
            var = self._new_var(self.name)
            local_vars[self.name] = var

        if isinstance(term, LiteralTerm):
            if var.value is None:
                var.value = term
            else:
                result = var.final_value() == term
        elif isinstance(term, VarTerm):
            if term.name in caller_vars:
                # Var defined in caller. Make them the same, if poss.
                caller = caller_vars[term.name]
                while isinstance(caller.value, VarArg):
                    caller = caller.value
                if caller.value is not None:
                    result = term.value == caller.final_value()
                else:
                    caller.value = self
        elif isinstance(term, ConsTerm):
            # Can't match a local variable to a cons term.
            result = False
        else:
            raise ValueError("can't bind VarArg to unrecognised type of term ?")
        return result


class ListConsArg(Arg):
    parts = ('head', 'tail')

    def __init__(self, spec):
        self.head = make_arg(spec[0])
        self.tail = make_arg(spec[1])

    @classmethod
    def is_valid_spec(cls, spec):
        # A split-list spec is a ListConsArg or a pair.
        return isinstance(spec, tuple) and len(spec) == 2

    def final_value(self):
        result = LiteralTerm([self.head.final_value()] + 
                             self.tail.final_value())
        return result

    def match_term(self, term, caller_vars, local_vars):
        result = True
        if isinstance(term, LiteralTerm):
            result = isinstance(term.value, list)
            if result:
                result = self.head.match_term(LiteralTerm(
                    term.value[0]), caller_vars, local_vars)
                if result:
                    result = self.tail.match_term(LiteralTerm(
                        term.value[1:]), caller_vars, local_vars)
        elif isinstance(term, VarTerm):
            # Can't match cons to var
            result = False
        elif isinstance(term, ConsTerm):
            result = isinstance(self.value, list)
            if result:
                result = self.head.match_term(
                    term.head, caller_vars, local_vars)
                if result:
                    result = self.tail.match_term(
                        term.tail, caller_vars, local_vars)
        else:
            raise ValueError("can't bind VarArg to unrecognised type of term ?")
        return result


class LiteralArg(Arg):
    parts = ('value',)
    @property
    def value(self):
        return self.spec

    @classmethod
    def is_valid_spec(cls, spec):
        # A literal spec is anything not a List-splitter or VarArg (for now).
        return not VarArg.from_spec(spec) and not ListConsArg.from_spec(spec)

    def match_term(self, term, caller_vars, local_vars):
        result = True
        if isinstance(term, LiteralTerm):
            result = term.value == self.value
        elif isinstance(term, VarTerm):
            if term.value is not None:
                result = term.value == self.value
            else:
                term.value = self.value
        elif isinstance(term, ConsTerm):
            result = isinstance(self.value, list)
            if result:
                result = LiteralArg(self.value[0]).match_term(
                    term.head, caller_vars, local_vars)
                if result:
                    result = LiteralArg(self.value[1:]).match_term(
                        term.tail, caller_vars, local_vars)
        else:
            raise ValueError("can't bind LiteralArg to unrecognised type of term ?")
        return result

    def __eq__(self, other):
        return self.value == other.value


class Rule(object):
    def __init__(self, args, terms=None):
        args = args or []
        terms = terms or []
        self.args = [make_arg(this) for this in args]
        self.call_terms = [make_term(this) for this in terms]

    def _args_match_call(self, args, local_vars, caller_vars):
        if len(args) != len(self.args):
            result = False
        else:
            result = True
            for arg, given_term in zip(self.args, args):
                if not arg.match_term(given_term, caller_vars, local_vars):
                    result = False
                    break
        return result

    def _form_caller_result(self, result, caller_vars):
        return {name:term.final_value() for name, term in caller_vars.items()}

    def possibles(self, args=None, ind=0):
        db(ind, '?TRY {}'.format(self))
        db(ind, ' -of-({}) ...'.format(args))
        local_vars, caller_vars = {}, {}
        if not self._args_match_call(args, local_vars, caller_vars):
            db(ind, '\NoRuleMatch')
        else:
            # satisfy all call_terms, recursively...
            for result in self._satisfy_call_terms(self.call_terms,
                                                   local_vars, ind+2):
                db(ind, '={}'.format(result))
                yield self._form_caller_result(result, caller_vars)
            db(ind, '\EndTerms')

    def _satisfy_call_terms(self, calls, context, ind=0):
        if len(calls) == 0:
            # No remaining calls: good to go.
            db(ind, '\Sat_Terms_Nomore')
            db(ind, '=term={}'.format(context))
            yield context  # return all local vars as-is
        else:
            this_call, rest_calls = calls[0], calls[1:]
            db(ind+2, 'Sat_Term {}'.format(this_call))
            for possible in this_call.possibles(context, ind+2):
#                db(ind+4, ':term_possible={}'.format(possible))
                possible_context = context.copy()
                possible_context.update(possible)
                for result in self._satisfy_call_terms(rest_calls,
                                                       possible_context,
                                                       ind+6):
                    db(ind+4, ':term_result={}'.format(result))
                    yield result
            db(ind+2, '\EndTerms')

    def __str__(self):
        str_args = ', '.join(str(arg) for arg in self.args)
        str_terms = ', '.join(str(term) for term in self.call_terms)
        return '<Rule({}): {}>'.format(str_args, str_terms)


class Term(ArgOrTerm):
    pass # abstract


class LiteralTerm(LiteralArg, Term):
    # Functionally equivalent, for now.
    pass


class VarTerm(VarArg, Term):
    # Functionally equivalent, for now.
    pass


class ConsTerm(ListConsArg, Term):
    # Functionally equivalent, for now.
    pass


#class TrueTerm(Term):
#    def possibles(self, context):
#        yield context
#
#    def __str__(self):
#        return '<TrueTerm>'
#
#class FalseTerm(Term):
#    def possibles(self, context):
#        if 0:
#            yield [1]
#
#    def __str__(self):
#        return '<FalseTerm>'


class CallTerm(ArgOrTerm):
    def __init__(self, pred, arg_specs):
        self.pred = pred
        self.arg_specs = [make_arg(spec) for spec in arg_specs]

    @classmethod
    def is_valid_spec(cls, spec):
        # Can't build from a spec : Use constructor instead.
        return False

    def possibles(self, context, ind=0):
        # Enumerate possible resolutions of this call within a context.
        # Context is local variables, which can have values or references.
        # Context may be updated with new (previously unseen) local variables.
        match_ok = True
        actual_args = []
        for arg in self.arg_specs:
            if isinstance(arg, VarArg):
                name = arg.name
                var = context.get(name)
                if var is None:
                    var = VarTerm._new_var(name)
                    context[name] = var
                arg_value = var.final_value()
            elif isinstance(arg, LiteralArg):
                arg_value = arg.final_value()
            else:
                msg = 'call argument {} has unhandled type {}.'
                raise ValueError(msg.format(arg, type(arg)))
            actual_args.append(arg_value)
        for result in self.pred.possibles(actual_args, ind+2):
            yield result

    def __str__(self):
        str_args = ', '.join(str(arg) for arg in self.arg_specs)
#        if not hasattr(self.pred, 'name'):
#            raise ValueError()
        return '<Call {}({})>'.format(self.pred.name, str_args)


class Pred(object):
    def __init__(self, name, rules=None):
        self.name = name
        self.rules = rules or []

    def add(self, rule_args, rule_terms=None):
        # TODO: allow passing existing contructed Rule ?
        self.rules.append(Rule(rule_args, rule_terms))

    def possibles(self, args, ind=0):
        for rule in self.rules:
            for result in rule.possibles(args, ind+2):
                yield result

    def __str__(self):
        str_rules = ', \n  '.join(str(rule) for rule in self.rules)
        return '<Pred {}({})>'.format(self.name, str_rules)

# Example...
# inlist(X, []) :- !, fail.
# inlist(X, [X|L]).
# inlist(X, [Y|L]) :- inlist(X, L).
# uniq([]).
# uniq([A|L]) :- not inlist(A, L), uniq(L).
#
# ? uniq(1, [2, 1, 3])

class FailPred(Pred):
    # Use as Call(Fail, [])
    def __init__(self):
        self.name = 'Fail'
        self.args = []
        self.rules = []

    def add(self, rule):
        raise NotImplementedError()

    def possibles(self, args, ind=0):
        # A generator that stops immediately.
        if 0:
            yield None

Fail = FailPred()

#class Succeed(Pred):
#    # Use as Call(Succeed, [])
#    def __init__(self, args):
#        self.name = 'Succeed'
#        self.args = []
#        self.rules = []
#
#    def add(self, rule):
#        raise NotImplementedError()
#
#    def possibles(self, args, context):
#        # A generator that succeeds once unconditionally.
#        yield context


class NotPred(Pred):
    # A predicate that succeeds once, unconditionally, iff the argument fails.
    # Use as Call(Not, [inner])
    def __init__(self):
        self.name = 'Not'
        self.args = [VarArg('_N')]
        self.rules = []

    def possibles(self, args, ind=0):
        inner_succeeded = False
        try:
            # See if there are any possibilities of our argument.
            next(args[0].possibles(context))
            inner_succeeded = True
        except StopIteration:
            pass
        if not inner_succeeded:
            yield {}

#    def __str__(self):
#        str_rules = ', \n  '.join(str(rule) for rule in self.rules)
#        return '<PredNOT({})>'.format(self.pred)

Not = NotPred()

def build_from_spec(spec, class_type_name, classes):
    for type in classes:
        if isinstance(spec, type):
            result = spec
        else:
            result = type.from_spec(spec)
        if result is not None:
            break
    if result is None:
        raise valueError('unexpected {} spec : "{!s}"'.format(
            class_type_name, spec))
    return result

def make_term(spec):
    return build_from_spec(spec, 'term', [VarTerm, CallTerm, LiteralTerm])

def make_arg(spec):
    return build_from_spec(spec, 'arg', [VarArg, ListConsArg, LiteralArg])


print make_arg(1.2)
print make_arg('xyz')
print make_arg('Xyz')
print make_arg(('head', 'Tail'))


# Example...
# inlist(X, []) :- !, fail.
# inlist(X, [X|L]).
# inlist(X, [Y|L]) :- inlist(X, L).
# uniq([]).
# uniq([A|L]) :- not inlist(A, L), uniq(L).
#
# ? uniq([1, 2, 1, 3])

Call = CallTerm
def Cons(head, tail):
    return ListConsArg((head, tail))

p_inlist = Pred('inlist')
p_inlist.add(('X', []),
             [Call(Fail, [])])
p_inlist.add(('X', Cons('X', 'L')),
             [])  # or [Call(True, [])]
p_inlist.add(('X', Cons('Y', 'L')),
             [Call(p_inlist, ['X', 'L'])])

p_uniq = Pred('uniq')
p_uniq.add(([],),
           [])
p_uniq.add((Cons('X', 'L'),),
           [Call(Not, [Call(p_inlist, ['X', 'L'])]),
            Call(p_uniq, ['L'])])

debug = True
test_calls = [
    (p_inlist, [1, [1]]),
]
#test_calls = [
#    (p_inlist, [2, [1, 2, 3]]),
#]
for test_call in test_calls:
    print
    print 'test {}'.format(test_call)
    pred, args = test_call
    args = [make_term(spec) for spec in args]
    for result_context in pred.possibles(args):
        print '   result : ', result_context
