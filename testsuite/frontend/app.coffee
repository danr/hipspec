window.hipspec_module = angular.module('hipspec', [])

hipspec_module.filter 'seconds', () -> (s) -> s.toFixed 2

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

hipspec_module.factory 'request', ($http) ->

    list: (testsuite) -> $http.get("#{testsuite}/json_list")

    log: (testsuite, instance) -> $http.get("#{testsuite}/#{instance}")

hipspec_module.controller 'TestsuiteCtrl', ($scope, config) ->

    $scope.testsuites = config

    $scope.testsuite = undefined
    $scope.selected = null

    $scope.setTestsuite = (v,n,fs) ->
        $scope.selected = null
        $scope.testsuite_name = n
        $scope.testsuite_files = fs
        $scope.testsuite = v

hipspec_module.controller 'CompareCtrl', ($scope, request, $http) ->

    $scope.content = ""
    $scope.viewFile = (dir,file) -> $http.get("#{dir}/#{file}").success (res) -> $scope.content = res

    $scope.table = {}
    $scope.headers = []
    $scope.num_solved = 0

    $scope.select = (id) -> $scope.selected = id

    $scope.display_prop = (prop) -> prop.replace /^prop_/, ""

    $scope.$watch 'testsuite', () -> if $scope.testsuite?
        request.list($scope.testsuite).success (list) ->
            $scope.headers = []
            $scope.table = {}
            $scope.num_solved = 0
            $scope.solved = {}
            for i in list
                do (i) ->
                    request.log($scope.testsuite, i).success (log) ->
                        for [ time, message ] in log
                            [[type,obj]] = _.pairs message
                            res = []
                            if type == "Finished"
                                $scope.headers = _.union($scope.headers, obj.proved, obj.unproved).sort()
                                for prop in $scope.headers
                                    res[prop] = _.contains obj.proved, prop
                                    if res[prop] and not $scope.solved[prop]
                                        $scope.solved[prop] = true
                                        $scope.num_solved++
                                res.time = time
                        console.log i
                        i.replace /^results/, ""
                        console.log i
                        $scope.table[i] = res


hipspec_module.controller 'InstanceCtrl', ($scope, $http, request) ->

    $scope.interestingType = (type) ->
        String _.contains ["FileProcessed","QuickSpecDone","InductiveProof","PlainProof","Finished"], type

    $scope.result = []
    $scope.$watch 'selected', () ->
        if $scope.selected?
            request.log($scope.testsuite,$scope.selected).success (x) ->
                res = []

                for [time, message] in x

                    [[type,obj]] = _.pairs message

                    if _.isArray obj
                        obj = {}

                    obj.time = time
                    obj.type = type

                    res.push obj

                $scope.result = res
        else
            $scope.result = []

