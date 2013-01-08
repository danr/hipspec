agder_module.directive 'markdown', () ->

    # http://blog.angularjs.org/2012/05/custom-components-part-1.html
    # http://jsfiddle.net/8bENp/66/
    converter = new Showdown.converter()
    link = (scope, element, attrs, model) ->
        render = () ->
            if model.$modelValue
                htmlText = converter.makeHtml model.$modelValue
            else
                htmlText = ""
            element.html(htmlText)

        scope.$watch attrs['ngModel'], render
        render()
    restrict: 'E'
    require: 'ngModel'
    link: link
