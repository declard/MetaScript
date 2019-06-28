refineFunc = mkIMacro [mkType "refine", expr', stmt', args', lval'] impl
  where expr' = mkT "Expression" (undefined, objectObj) [number',  string', array', object', lambda', application', operator', block', if', ifelse', unit']
        number' = mkT "Number" expr' []
        string' = mkT "String" expr' []
        array' = mkT "Array" expr' []
        object' = mkT "Object" expr' []
        lambda' = mkT "Lambda" expr' []
        application' = mkT "Application" expr' []
        operator' = mkT "Operator" expr' []
        block' = mkT "Block" expr' []
        if' = mkT "If" expr' []
        ifelse' = mkT "IfElse" expr' []
        unit' = mkT "Unit" expr' []
        args' = mkT "Arguments" (undefined, objectObj) [fixed', variadic']
        fixed' = mkT "Fixed" args' []
        variadic' = mkT "Variadic" args' []
        stmt' = mkT "Statement" (undefined, objectObj) [define', while', for', function', set', exec']
        define' = mkT "Define" stmt' []
        while' = mkT "While" stmt' []
        for' = mkT "For" stmt' []
        function' = mkT "Function" stmt' []
        set' = mkT "Set" stmt' []
        exec' = mkT "Exec" stmt' []
        lval' = mkT "LValue" (undefined, objectObj) [static', virtual', identifier']
        static' = mkT "Static" lval' []
        virtual' = mkT "Virtual" lval' []
        identifier' = mkT "Identifier" lval' []
        mkT name (_, proto) fields = (String name, mkRObj (mkType name : (primitive prototypeObj, proto) : fields))
        n name value = (String name, value)
        impl Nothing [e] = refine e
        impl _ _ = argsE "refine"
        mkNode (_, p) n f = allocateObject $ (primitive prototypeObj, p) : mkType n : f
        refine :: P.Expression -> Evaluation Object
        refine (P.Number num) = mkNode expr' "Number" [n "value" $ mkNumber num]
        refine (P.String str) = mkNode expr' "String" [n "value" $ mkString str]
        refine (P.Array exprs) = do
          elements <- mapM refine exprs
          array <- allocateArray elements
          mkNode expr' "Array" [n "elements" array]
        refine (P.Object pairs) = do
          fields <- mapM (\(k, v) -> do { ko <- refine k; vo <- refine v; mkPair (ko, vo) }) pairs
          array <- allocateArray fields
          mkNode expr' "Object" [(String "fields", array)]
        refine (P.Lambda args body) = do
          argso <- refineArgs args
          bodyo <- refine body
          mkNode expr' "Lambda" [(String "arguments", argso), (String "body", bodyo)]
        refine (P.Application func args) = do
          funco <- refine func
          argso <- mapM refine args
          array <- allocateArray argso
          mkNode expr' "Application" [(String "function", funco), (String "arguments", array)]
        refine (P.Operator left op right) = do
          lefto <- refine left
          righto <- refine right
          mkNode expr' "Operator" [(String "name", mkString op), (String "left", lefto), (String "right", righto)]
        refine (P.Block stmts) = do
          stmtso <- mapM refineStmt stmts
          array <- allocateArray stmtso
          mkNode expr' "Block" [(String "statements", array)]
        refine (P.If c t) = do
          co <- refine c
          to <- refine t
          mkNode expr' "If" [(String "clause", co), (String "thenCase", to)]
        refine (P.IfElse c t e) = do
          co <- refine c
          to <- refine t
          eo <- refine e
          mkNode expr' "IfElse" [(String "clause", co), (String "thenCase", to), (String "elseCase", eo)]
        refine (P.LValue lvalue) = refineLVal lvalue
        refine (P.Unit) = mkNode expr' "Unit" []
        refineArgs (P.Fixed args) = do
          array <- allocateArray $ map mkString args
          mkNode args' "Fixed" [(String "list", array)]
        refineArgs (P.Variadic arg) = mkNode args' "Variadic" [(String "name", mkString arg)]
        refineStmt (P.Define name value) = do
          valueo <- refine value
          mkNode stmt' "Define" [(String "name", mkString name), (String "value", valueo)]
        refineStmt (P.While clause block) = do
          clauseo <- refine clause
          blocko <- refine block
          mkNode stmt' "While" [(String "clause", clauseo), (String "block", blocko)]
        refineStmt (P.For kname vname source block) = do
          sourceo <- refine source
          blocko <- refine source
          mkNode stmt' "For" [(String "keyName", mkString kname), (String "valueName", mkString vname), (String "source", sourceo), (String "block", blocko)]
        refineStmt (P.Function name args block) = do
          blocko <- refine block
          array <- allocateArray $ map mkString args
          mkNode stmt' "Function" [(String "name", mkString name), (String "args", array), (String "block", blocko)]
        refineStmt (P.Set lval value) = do
          lvalo <- refineLVal lval
          valueo <- refine value
          mkNode stmt' "Set" [(String "target", lvalo), (String "value", valueo)]
        refineStmt (P.Execute value) = do
          valueo <- refine value
          mkNode stmt' "Exec" [(String "value", valueo)]
        refineLVal (P.Static object idx) = do
          objecto <- refine object
          idxo <- refine idx
          mkNode lval' "Static" [(String "object", objecto), (String "index", idxo)]
        refineLVal (P.Virtual object idx) = do
          objecto <- refine object
          idxo <- refine idx
          mkNode lval' "Virtual" [(String "object", objecto), (String "index", idxo)]
        refineLVal (P.Identifier name) = do
          mkNode lval' "Identifier" [(String "name", mkString name)]