agder_module.controller('ProblemsCtrl', ($scope,$http,make_url,$q) ->

        $scope.problems = $q.defer()

        # $scope.problems.resolve ['DeMorgan']

        # $scope.problems =

        $http.get(make_url "/problems").success (x) ->
            console.log x
            $scope.problems.resolve x...

        ###
        .error(console.log)
        .success (res) -> $scope.problems = res
        ###

    ).controller 'ProblemCtrl', ($scope,$http,$location,$rootScope,make_url) ->
        # The identifier of this problem
        $id = $scope.id

        angular.extend $scope,
            # These are set in updateShow below
            problem:  ""
            definitions: ""
            description: ""
            #The result of a problem
            result: ""
            solved: false

        # Problem showed or not is in $scope.show
        # This is in the location bar
        $scope.loc = $location

        $scope.$watch 'loc.search()', () ->
            $scope.show = $location.search()[$id]?
            $scope.updateShow()

        $scope.$watch 'show', () ->
            $location.search($id, $scope.show or null)

        $scope.toggleShow = () ->
            $scope.show = !$scope.show
            $scope.updateShow()

        $scope.updateShow = () ->
            if $scope.show and not $scope.problem
                $http.get(make_url "/problem/#{$id}")
                    .error(console.log)
                    .success (res) -> angular.extend $scope,
                        problem: res.problem
                        definitions: res.definitions or ""
                        description: res.description or ""

        $scope.cred = () -> $rootScope.credentials

        $scope.$watch "cred()", (u) ->
            console.log "#{$id} knows credentials has changed. Status is #{$rootScope.status}"

        # Solution attempt
        $scope.submit = () ->
            $scope.result = "Submitted!"
            $http.post(make_url("/solve/#{$id}"),
                credentials: credentials.get()
                solution: $scope.problem
            ).error(console.log).success (res) ->

                status = credentials.parse_status res.user_status

                if status == "CredentialsOK"

                    $scope.result = res.stdout.replace ////home/dan/code/agder/solutions/#{$id}/[^/]*/([^\.]*).agda///g, (filename, short) ->
                        short + ".agda"

                    if res.exitcode == 0
                        $scope.solved = true

                else

                    $scope.result = status


