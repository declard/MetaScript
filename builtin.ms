function dispatch funcs {
  args => {
    var ac = args.length()
    function tryWith(pred) {
      var matches = funcs.filter((f) => p(f.argsCount().somethingOrNull))
      var ml = matches.length()
      if (ml == 1) Identity(matches.pop().applyPoly(args)) else
      if (ml > 1) Error('Ambiguous function list in dispatch') else
      null
    }
    tryWith((f) => f((v) => v == ac, const(false))).onNull(
      const(tryWith((f) => f(const(false), const(true)))))
  }
}