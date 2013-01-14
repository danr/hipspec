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

    prod:
        name: 'Productive Use of Failure'
        files: ['Definitions.hs', 'Properties.hs']
    zeno:
        name: 'Zeno/IsaPlanner'
        files: ['Definitions.hs', 'Properties.hs']
    mini:
        name: 'Mini'
        files: ['Mini.hs']

    examples:
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

    'precision-recall':
        name: 'Precision/Recall'
        files: []

hipspec_module.factory 'request', ($http) ->

    list: (testsuite) -> $http.get("#{testsuite}/json_list")

    log: (testsuite, instance) -> $http.get("#{testsuite}/#{instance}")

hipspec_module.controller 'TestsuiteCtrl', ($scope, config) ->

    $scope.empty = _.isEmpty

    $scope.testsuites = config

    $scope.testsuite = undefined
    $scope.selected = null

    $scope.setTestsuite = (v,n,fs) ->
        $scope.selected = null
        $scope.testsuite_name = n
        $scope.testsuite_files = fs
        $scope.testsuite = v

hipspec_module.controller 'CompareCtrl', ($scope, request, $http, $q) ->

    $scope.content = ""
    $scope.viewFile = (dir,file) -> $http.get("#{dir}/#{file}").success (res) -> $scope.content = res

    $scope.table = {}
    $scope.headers = {}
    $scope.num_solved = 0
    $scope.solved = {}

    $scope.display_prop = (prop) -> prop.replace /^prop_/, ""

    $scope.num_problems = () -> _.size $scope.headers

    $scope.$watch 'testsuite', () -> if $scope.testsuite?
        request.list($scope.testsuite).success (list) ->
            $scope.headers = {}
            $scope.table = {}
            $scope.num_solved = 0
            $scope.solved = {}

            u = $q.all(request.log($scope.testsuite, i) for i in list)

            u.then (logs) ->
                headers = {}
                table = {}
                num_solved = 0
                solved = {}
                for [i,http_res] in _.zip(list,logs)
                    log = http_res.data
                    # console.log i, log
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

                # console.log num_solved, solved, headers, table

                $scope.headers = headers
                $scope.table = table
                $scope.num_solved = num_solved
                $scope.solved = solved



hipspec_module.controller 'InstanceCtrl', ($scope, $http, request) ->

    $scope.interestingType = (type) ->
        String _.contains ["FileProcessed","QuickSpecDone","InductiveProof","PlainProof","Finished"], type

    $scope.result = []
    $scope.show = false

    $scope.toggle_shown = ->
        $scope.show = !$scope.show
        if _.isEmpty $scope.result
            request.log($scope.testsuite,$scope.instance).success (x) ->
                res = []

                for [time, message] in x

                    [[type,obj]] = _.pairs message

                    if _.isArray obj
                        obj = {}

                    obj.time = time
                    obj.type = type

                    res.push obj

                $scope.result = res

