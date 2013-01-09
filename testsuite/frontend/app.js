// Generated by CoffeeScript 1.4.0
(function() {

  window.hipspec_module = angular.module('hipspec', []);

  hipspec_module.filter('seconds', function() {
    return function(s) {
      return s.toFixed(2);
    };
  });

  hipspec_module.factory('config', function() {
    return {
      prod: {
        name: 'Productive Use of Failure',
        files: ['Definitions.hs', 'Properties.hs']
      },
      zeno: {
        name: 'Zeno/IsaPlanner',
        files: ['Definitions.hs', 'Properties.hs']
      },
      mini: {
        name: 'Mini',
        files: ['Mini.hs']
      },
      examples: {
        name: 'Examples',
        files: ['AppendLists.hs', 'BinLists.hs', 'Implies.hs', 'ListMonad.hs', 'Nat.hs', 'Nicomachus.hs', 'Reverse.hs', 'Rotate.hs']
      }
    };
  });

  hipspec_module.factory('request', function($http) {
    return {
      list: function(testsuite) {
        return $http.get("" + testsuite + "/json_list");
      },
      log: function(testsuite, instance) {
        return $http.get("" + testsuite + "/" + instance);
      }
    };
  });

  hipspec_module.controller('TestsuiteCtrl', function($scope, config) {
    $scope.testsuites = config;
    $scope.testsuite = void 0;
    $scope.selected = null;
    return $scope.setTestsuite = function(v, n, fs) {
      $scope.selected = null;
      $scope.testsuite_name = n;
      $scope.testsuite_files = fs;
      return $scope.testsuite = v;
    };
  });

  hipspec_module.controller('CompareCtrl', function($scope, request, $http) {
    $scope.content = "";
    $scope.viewFile = function(dir, file) {
      return $http.get("" + dir + "/" + file).success(function(res) {
        return $scope.content = res;
      });
    };
    $scope.table = {};
    $scope.headers = [];
    $scope.num_solved = 0;
    $scope.select = function(id) {
      return $scope.selected = id;
    };
    $scope.display_prop = function(prop) {
      return prop.replace(/^prop_/, "");
    };
    return $scope.$watch('testsuite', function() {
      if ($scope.testsuite != null) {
        return request.list($scope.testsuite).success(function(list) {
          var i, _i, _len, _results;
          $scope.headers = [];
          $scope.table = {};
          $scope.num_solved = 0;
          $scope.solved = {};
          _results = [];
          for (_i = 0, _len = list.length; _i < _len; _i++) {
            i = list[_i];
            _results.push((function(i) {
              return request.log($scope.testsuite, i).success(function(log) {
                var message, obj, prop, res, time, type, _j, _k, _len1, _len2, _ref, _ref1, _ref2;
                for (_j = 0, _len1 = log.length; _j < _len1; _j++) {
                  _ref = log[_j], time = _ref[0], message = _ref[1];
                  _ref1 = _.pairs(message)[0], type = _ref1[0], obj = _ref1[1];
                  res = [];
                  if (type === "Finished") {
                    $scope.headers = _.union($scope.headers, obj.proved, obj.unproved).sort();
                    _ref2 = $scope.headers;
                    for (_k = 0, _len2 = _ref2.length; _k < _len2; _k++) {
                      prop = _ref2[_k];
                      res[prop] = _.contains(obj.proved, prop);
                      if (res[prop] && !$scope.solved[prop]) {
                        $scope.solved[prop] = true;
                        $scope.num_solved++;
                      }
                    }
                    res.time = time;
                  }
                }
                console.log(i);
                i.replace(/^results/, "");
                console.log(i);
                return $scope.table[i] = res;
              });
            })(i));
          }
          return _results;
        });
      }
    });
  });

  hipspec_module.controller('InstanceCtrl', function($scope, $http, request) {
    $scope.interestingType = function(type) {
      return String(_.contains(["FileProcessed", "QuickSpecDone", "InductiveProof", "PlainProof", "Finished"], type));
    };
    $scope.result = [];
    return $scope.$watch('selected', function() {
      if ($scope.selected != null) {
        return request.log($scope.testsuite, $scope.selected).success(function(x) {
          var message, obj, res, time, type, _i, _len, _ref, _ref1;
          res = [];
          for (_i = 0, _len = x.length; _i < _len; _i++) {
            _ref = x[_i], time = _ref[0], message = _ref[1];
            _ref1 = _.pairs(message)[0], type = _ref1[0], obj = _ref1[1];
            if (_.isArray(obj)) {
              obj = {};
            }
            obj.time = time;
            obj.type = type;
            res.push(obj);
          }
          return $scope.result = res;
        });
      } else {
        return $scope.result = [];
      }
    });
  });

}).call(this);
