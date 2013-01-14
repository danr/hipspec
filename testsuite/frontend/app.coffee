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


hipspec_module.factory 'config', () ->

    [
        short: 'prod'
        name: 'Productive Use of Failure'
        files: ['Definitions.hs', 'Properties.hs']
    ,
        short: 'zeno'
        name: 'Zeno/IsaPlanner'
        files: ['Definitions.hs', 'Properties.hs']
    ,
        short: 'mini'
        name: 'Mini'
        files: ['Mini.hs']
    ,
        short: 'examples'
        name: 'Examples'
        files:
            [ 'AppendLists.hs'
              'BinLists.hs'
              'Implies.hs'
              'ListMonad.hs'
              'Nat.hs'
              'Nicomachus.hs'
              'Reverse.hs'
              'Rotate.hs'
            ]

    ,
        short: 'precision-recall'
        name: 'Precision/Recall'
        files: []
    ]

hipspec_module.factory 'request', ($http) ->

    list: (testsuite) -> $http.get "#{testsuite.short}/json_list"

    log: (testsuite, instance) -> $http.get "#{testsuite.short}/#{instance}"

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
            for [ time, message ] in log
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
            table[i] = res
        $scope.headers = headers
        $scope.table = table
        $scope.num_solved = num_solved
        $scope.solved = solved

    $scope.$watch 'testsuite', () -> if $scope.testsuite?
        request.list($scope.testsuite).success (list) ->
            empty()
            $q.all(request.log($scope.testsuite, i) for i in list).then (logs) ->
                $scope.results = _.object list, _.map logs, (res) -> res.data
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
                    $scope.equations = obj.equations
                    $scope.explored = true
                    $scope.exploration_time = time
                    break
            $scope.processed = true
        return $scope.explored

hipspec_module.controller 'InstanceCtrl', ($scope) ->

    $scope.interestingType = (type) ->
        String _.contains ["FileProcessed","QuickSpecDone","InductiveProof","PlainProof","Finished","ExploredTheory"], type

    $scope.result = []
    $scope.show = false

    $scope.toggle_shown = (instance) ->
        $scope.show = !$scope.show
        x = $scope.results[instance]
        res = []

        for [time, message] in x

            [[type,obj]] = _.pairs message

            if _.isArray obj
                obj = {}

            obj.time = time
            obj.type = type

            res.push obj

        $scope.result = res

