#
# mechanism
#
def Pred__possibles(args):
    for rule in self.rules:
        for possible in rule.possibles(args):
            yield possible

def Rule__possibles(args):
    locals = self.match_args(self.args, args)
    if locals is None:
        return
    # E.G. "pred(X, 1)" matches ("Q", "V") producing {'X':Var("Q"), 'V':Lit(1)}
    #   (and returns [X, 1])
    for term in self.terms:
        local, term_args = term.fill_args(locals)
        # E.G. "call(X, V, 3)" matches from {'X':Var("Q"),'V':Lit(1)}
        #   producing {X:Q, V:1} and returning [X, 1, 3]
        # E.G. "call(X, Z)" with {X:Q, V:1} matches [Q, Z] yielding {X:Q, V:1, Z:V(xxx)}
        #  and then P(Z) would match [Z].
        for possible in term.pred.possibles(term_args):  # NB *not* locals
            yield possible

def Rule__match_args(args):
    vars = {}
    for arg in self.args:
        vars = arg.match_vars(arg, vars)  # None if fail
        if vars is None:
            break
    return vars

_uid = 0
def new_temp_var(basename):
    uid += 1
    name = name + '_' + str(uid)
    return Var(name)

def Term__fill_args(vars):
    args = []
    for arg in self.args:
        # E.G. I(4) returns (I(4))
        # E.G. V('X') pulls from {X:3} returning (I(3))
        # E.G. V('Z') pulls from {V:Z} returning (V(Z))
        # E.G. V('Q') adds {Q:V()}
        if isinstance(arg, VarArg):
            if arg.name not in vars:
                vars[arg.name] = new_temp_var(arg.name)
                arg = vars[arg.name]
        elif isintance(arg, LiteralArg):
            pass
        else:
            raise ValueError()
        args.append(arg)
    return args

def LiteralArg__match_term(term, vars):
    if isinstance(term, LiteralArg):
        # E.G. f(X, 2) ?match (_Y, Lit(?))
        if self.value == term.value:
            # E.G. f(X, 2) ?match (_Y, 2)
            pass  # ok
        else:
            # E.G. f(X, 2) ?match (_Y, 3)
            vars = None  # fail
    elif isinstance(term, VarArg):
        # E.G. f(X, 2) ?match f(_Y, Q)
        existing = vars.get(term.name)
        if not existing:
            # E.G. f(X, 2) ?match f(_Y, _Q)
            vars[term.name] = term
        elif vars[term].value == self.value:
            # E.G. f(X, 2) ?match f(_Y, Z)
            pass
        else
    return vars

def VarArg__match_term(term, vars):
    name = self.name
    if isinstance(term, LiteralArg):
        # E.G. f(X) ?match (3)
        if name in vars:
            vars[name] = new_temp_var(name)
        vars[name] = term
    elif isinstance(term, VarArg):
        existing = vars.get(self.name)
        if not existing:
            vars[self.name] = term
        else:
            raise ValueError
    return vars

def ConsArg__match_term(term, vars):
    if (isinstance(term, LiteralTerm) and
        isinstance(term.value, list) and len(term.value) > 0):
            vars = self.head.match_vars(make_term(term.value[0]), vars)
            if vars is not None:
                vars = self.tail.match_vars(make_term(term.value[1:]), vars)
            else:
                raise ValueError
    return vars


