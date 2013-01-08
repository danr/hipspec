agder_module.factory 'credentials', ($http, make_url, $rootScope) ->

    hash = (salt, password) -> CryptoJS.SHA256(salt + password).toString(CryptoJS.enc.Hex)

    update_credentials = (status, username, h) ->
        $rootScope.status = status
        $rootScope.credentials = if $rootScope.status == "CredentialsOK"
                Credentials:
                    cred_user: username
                    cred_hash: h
            else
                Anonymous: []

    logout = () -> update_credentials "NotLoggedIn"

    logout()

    parse_status = (res) ->
        for key of res
            return key
        return "NotLoggedIn"

    get_salt = (username, cont) ->
        $http.post(make_url("/salt"), d: username)
            .error(console.log)
            .success cont

    register = (username, password) ->
        get_salt username, (salt) ->
            $http.post(make_url("/register"),
                Credentials:
                    cred_user: username
                    cred_hash: hash(salt, password)
            ).success (res) ->
                $rootScope.status = parse_status res
                if $rootScope.status == "SuccessfulCreation"
                    login username, password

    login = (username, password) ->
        get_salt username, (salt) ->
            h = hash(salt, password)
            $http.post(make_url("/login"),
                Credentials:
                    cred_user: username
                    cred_hash: h
            ).success (res) ->
                update_credentials (parse_status res), username, h

    register: register
    login: login
    logout: logout


