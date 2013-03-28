window.hipspec_module = angular.module('hipspec', [])

hipspec_module.filter 'seconds', () -> (s) ->
    if s?
        s.toFixed 2
    else
        ""

hipspec_module.filter 'ppresfile', () -> (s) ->
    s = s.replace /^results\//, -> ""
    s = s.replace /.json$/, -> ""
    s.replace /_/g, -> " "

hipspec_module.filter 'display_prop', () -> (s) ->
    s = s.replace /^prop_/, ""
    s = s.replace /^Prop/, ""
    s.replace /.hs$/, ""

hipspec_module.factory 'config', () ->

    [
        short: 'prod'
        name: 'Productive Use of Failure'
        files: ['Definitions.hs', 'Properties.hs']
    ,
        short: 'prod'
        name: "Zeno's result on Productive Use of Failure"
        files: []
        zeno_style: true
    ,
        short: 'zeno'
        name: 'Zeno/IsaPlanner'
        files: ['Definitions.hs', 'Properties.hs']
    ,
        short: 'examples'
        name: 'Examples'
        files:
            [ 'Nicomachus.hs'
              'Reverse.hs'
              'Rotate.hs'
            ]

    ,
        short: 'precision-recall'
        name: 'Precision/Recall'
        files: [ 'PrecisionRecall.hs' ]
    ]

hipspec_module.factory 'request', ($http) ->

    zeno_style: (testsuite) -> $http.get "#{testsuite.short}/zeno_results.json"

    results: (testsuite) -> $http.get "#{testsuite.short}/result.json"

hipspec_module.controller 'TestsuiteCtrl', ($scope, config) ->

    $scope.empty = _.isEmpty

    $scope.testsuites = config

    $scope.testsuite = undefined

    $scope.setTestsuite = (t) -> $scope.testsuite = t

hipspec_module.controller 'CompareCtrl', ($scope, request, $http, $q) ->

    $scope.content = ""
    $scope.viewFile = (dir,file) -> $http.get("#{dir}/#{file}").success (res) -> $scope.content = res

    empty = () ->
        $scope.table = {}
        $scope.headers = {}
        $scope.num_solved = 0
        $scope.solved = {}

    $scope.display_prop = (prop) -> prop.replace /^prop_/, ""

    $scope.num_problems = () -> _.size $scope.headers

    $scope.results = {}

    process_results = () ->
        table = {}
        headers = {}
        num_solved = 0
        solved = {}
        for i, log of $scope.results
            if i == "dummy" then continue
            for [ time, message ] in log
                # console.log time, message
                [[type,obj]] = _.pairs message
                res = {}
                if type == "Finished"
                    for prop in obj.unproved
                        headers[prop] = {}
                        res[prop] =
                            solved: false
                            failed: true
                    for prop in obj.proved
                        headers[prop] = {}
                        res[prop] =
                            solved: true
                            failed: false
                        if res[prop].solved and not solved[prop]
                            solved[prop] = true
                            num_solved++
                    res.time = time
            console.log res
            table[i] = res
        $scope.headers = headers
        $scope.table = table
        $scope.num_solved = num_solved
        $scope.solved = solved

    $scope.$watch 'testsuite', () ->
        if $scope.testsuite?
            if $scope.testsuite.zeno_style
                request.zeno_style($scope.testsuite).success (list) ->
                    $scope.table = {}
                    headers = {}
                    num_solved = 0
                    solved = {}
                    for prop, result of list
                        headers[prop] = {}
                        success = result == "true"
                        # res[prop] =
                        #     solved: success
                        #     failed: !success
                        if success
                            solved[prop] = true
                            num_solved++
                    $scope.headers = headers
                    $scope.num_solved = num_solved
                    $scope.solved = solved
            else
                request.results($scope.testsuite).success (res) ->
                    empty()
                    console.log res
                    $scope.results = res
                    process_results()

hipspec_module.controller 'ExplorationCtrl', ($scope) ->

    $scope.equations = []
    $scope.explored = false
    $scope.processed = false
    $scope.exploration_time = 0

    $scope.is_explored = (instance) ->
        if not $scope.processed
            for [time, message] in $scope.results[instance]
                [[type,obj]] = _.pairs message
                if type == "ExploredTheory"
                    $scope.equations = obj
                    $scope.explored = true
                    $scope.exploration_time = time
                    break
            $scope.processed = true
        return $scope.explored

hipspec_module.controller 'InstanceCtrl', ($scope) ->

    $scope.interestingType = (type) ->
        String _.contains ["FileProcessed","QuickSpecDone","InductiveProof","PlainProof","FailedProof","Finished","ExploredTheory"], type

    $scope.empty = (x) -> _.isEmpty(x)

    $scope.result = []
    $scope.show = false

    $scope.toggle_shown = (instance) ->
        $scope.show = !$scope.show

        x = $scope.results[instance]
        res = []

        for [time, message] in x

            [[type,obj]] = _.pairs message

            console.log type, obj
            if type == "InductiveProof" and _.isEmpty obj.vars
                console.log "Setting plain proof"
                type = "PlainProof"

            if _.isArray obj
                obj = {}

            obj.time = time
            obj.type = type

            res.push obj

        $scope.result = res

