window.hipspec_module = angular.module('hipspec', [])

hipspec_module.filter 'seconds', () -> (s) -> s.toFixed 2

hipspec_module.factory 'request', ($http) ->

    list: (testsuite) -> $http.get("#{testsuite}/json_list")

    log: (testsuite, instance) -> $http.get("#{testsuite}/#{instance}")

hipspec_module.controller 'TestsuiteCtrl', ($scope) ->

    $scope.testsuite = undefined

    $scope.setTestsuite = (v) ->
        $scope.testsuite = v

hipspec_module.controller 'CompareCtrl', ($scope, request) ->

    $scope.table = {}
    $scope.headers = []

    $scope.selected = null
    $scope.select = (id) -> console.log $scope.selected = id

    $scope.display_prop = (prop) -> prop.replace /^prop_/, ""

    $scope.$watch 'testsuite', () -> if $scope.testsuite?
        request.list($scope.testsuite).success (list) ->
            $scope.headers = []
            $scope.table = {}
            for i in list
                do (i) ->
                    console.log i
                    request.log($scope.testsuite, i).success (log) ->
                        for [ time, message ] in log
                            [[type,obj]] = _.pairs message
                            res = []
                            if type == "Finished"
                                if _.isEmpty $scope.headers
                                    $scope.headers = [].concat(obj.proved, obj.unproved).sort()
                                    console.log $scope.headers
                                for prop in $scope.headers
                                    res[prop] = _.contains obj.proved, prop
                                res.time = time
                        $scope.table[i] = res
                        console.log i, $scope.table


hipspec_module.controller 'InstanceCtrl', ($scope, $http, request) ->

    $scope.interestingType = (type) ->
        String _.contains ["FileProcessed","QuickSpecDone","InductiveProof","PlainProof","Finished"], type

    $scope.result = {}
    $scope.$watch 'selected', () -> if $scope.selected?
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

