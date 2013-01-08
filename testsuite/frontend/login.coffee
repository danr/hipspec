agder_module.controller 'LoginCtrl', ($scope,$rootScope,credentials) ->

    $scope.username = ""
    $scope.password = ""

    $scope.logged_in = () -> $rootScope.status == "CredentialsOK"

    $scope.execute = (fn) -> () ->
        fn $scope.username, $scope.password

    $scope.register = $scope.execute(credentials.register)
    $scope.login = $scope.execute(credentials.login)
    $scope.logout = ->
        $scope.username = ""
        $scope.password = ""
        $scope.execute(credentials.logout)()

