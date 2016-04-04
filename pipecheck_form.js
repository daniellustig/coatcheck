$(function() {
  $("body").layout({
    north__resizable: false,
    north__closable: false,
    east__size: "49%",
    east__onresize: function () {
      $("#graph-div").css("width", "100%")
        .css("height", "100%").css("height", "-=50px)");
    }
  });
})

function resetAll(clearLogs) {
  if (typeof worker == 'undefined') {
    //console.log("No workers have been launched");
  } else {
    worker.terminate();
  }
  if (typeof grapher == 'undefined') {
    //console.log("No graphers have been launched");
  } else {
    grapher.terminate();
  }

  $("#graph-div").empty();

  $("#graphbutton").button({
    disabled: true
  }).off("click");
  $("#resulttext").text("");

  if (clearLogs) {
    $("#log").val("");
    $("#result").val("");
    $("#latest-log-entry").text("Welcome! To begin, choose a model, choose a test, and click submit!");
  }

  modelEditor.setReadOnly(false);

  $("#run-button").button({
    disabled: false
  });
}

function restoreGraph() {
  if (typeof my_zoom === 'undefined') {
    console.log("Graph doesn't exist yet; can't reset it");
  } else {
    my_zoom.translate([original_translate[1], original_translate[2]]);
    my_zoom.scale(1);
    my_zoom.event(d3.select(document.getElementById("graph-outer")));
  }
}

function updateTest() {
  $("#maxtests").text("");
  var test = $("#testselect").val();
  if (test == "") {
    $("#testselect").val(last_test);
  } else if (availableTags.indexOf(test) >= 0) {
    last_test = test;
    var target = "tests/" + test + ".test";
    $.get(target, function(response) {
      try {
        restored = response
        testEditor.setValue(restored);
        testEditor.clearSelection();
        testEditor.gotoLine(0, 0, true);
      } catch (err) {
        console.log(err);
        testEditor.setValue("(ERROR: file " + target + ")");
        testEditor.clearSelection();
        testEditor.gotoLine(0, 0, true);
      };
    });
  } else {
    last_test = test;
    testEditor.setValue("");
    testEditor.clearSelection();
    logAppend("Unknown test " + test + "\n");
  }
}

function updateModel() {
  var target = $("#modelselect").val();
  if (target == "") {
    $("#modelselect").val(modelPrevious);
  } else if (availableModels.indexOf(target) >= 0) {
    if (modelModified) {
      $("#modelDialog").dialog("open");
    } else {
      $.get("uarches/" + target, function(d) {
        modelEditor.setValue(d);
        modelEditor.clearSelection();
        modelEditor.gotoLine(0, 0, true);
        modelPrevious = target;
        modelModified = false;
        $("#modelModified").html("");
        $(":focus").blur();
      });
    }
  } else {
    modelPrevious = target;
    modelEditor.setValue("");
    modelEditor.clearSelection();
    modelModified = false;
    logAppend("Unknown model " + target + "\n");
  }
}

$(function() {
  window.onbeforeunload = function() {
    if (typeof modelModified == 'undefined') {
      return;
    } else {
      if (modelModified) {
        return "The model has been modified; are you sure you want to close the window?";
      } else {
        return;
      }
    }
  };
});


$(function() {
  $("#modelDialog").dialog({
    autoOpen: false,
    resizable: false,
    height: 200,
    modal: true,
    buttons: {
      "Discard and Reload": function() {
        modelModified = false;
        updateModel();
        $(this).dialog("close");
      },
      "Cancel": function() {
        $("#modelselect").val(modelPrevious);
        $(this).dialog("close");
      }
    }
  });
  $("#modelDialog").html("The (micro)architecture model has been modified." +
    "  Are you sure you want to discard your changes and load in the new model?");

  modelEditor = ace.edit("model-editor");
  modelEditor.setTheme("ace/theme/github");
  //modelEditor.getSession().setMode("ace/mode/javascript");
  modelEditor.$blockScrolling = Infinity

  modelEditor.getSession().on('change', function(e) {
    modelModified = true;
    $("#modelModified").html("(modified)");
  });

  $("#model").resizable({
    handles: "s",
    resize: function(event, ui) {
      modelEditor.resize();
    }
  });

  testEditor = ace.edit("test-editor");
  testEditor.setTheme("ace/theme/github");
  //testEditor.getSession().setMode("ace/mode/javascript");
  testEditor.$blockScrolling = Infinity

  $("#test").resizable({
    handles: "s",
    resize: function(event, ui) {
      testEditor.resize();
    }
  });

  $("#logdiv").resizable({
    handles: "s",
  });

  resetAll(true);

  testEditor.clearSelection();
  testEditor.gotoLine(0, 0, false);
  //testEditor.setReadOnly(true);

  $("#graphbutton").button({
    disabled: true
  });

  $("#run-button").button().click(runPipeCheck);
  $("#reset-button").button().click(function() {
    resetAll(true);
  });
});

function logAppend(v) {
  var log = $("#log");
  log.val(log.val() + v);
  $("#latest-log-entry").text(v);
}

function runPipeCheck() {
  result = document.getElementById("result");
  log = document.getElementById("log");

  modelEditor.setReadOnly(true);

  result.value = "Running...";
  $("#resulttext").text("Running...").removeClass("stricter weaker");
  $("#log").val("");
  logAppend("Running...\n");
  $("#run-button").button({
    disabled: true
  });

  $("#graph-outer").text("");

  worker = new Worker("./worker.js");

  worker.onmessage = function(e) {
    if (e.data.type == "log") {
      logAppend(e.data.message);
    } else if (e.data.type == "result") {
      if (e.data.result.allowed) {
        if (e.data.result.observable) {
          $("#resulttext").text("Permitted/Observable")
            .removeClass("stricter weaker");
        } else {
          $("#resulttext").text("Permitted/Not Observable")
            .addClass("stricter");
        }
        logAppend("Outcome permitted\n");
      } else {
        if (e.data.result.observable) {
          $("#resulttext").text("Forbidden/Observable")
            .addClass("weaker");
        } else {
          $("#resulttext").text("Forbidden/Not Observable")
            .removeClass("stricter weaker");
        }
        logAppend("Outcome forbidden\n");
      }
      if (e.data.result.observable) {
        $("#graphbutton").button({
          disabled: true
        }).off("click");
        logAppend("Drawing graph (this may take a few seconds...)\n");
        result.value = e.data.result.graph;

        grapher = new Worker("./grapher.js");

        grapher.onmessage = function(e) {
          if (e.data.result == "error")
          {
            console.log(e.data.msg);
            logAppend("Graph failed to render! Sorry! Please contact the authors!\n");
            $("#graphbutton").button({
              disabled: true
            }).off("click");
            $("#run-button").button({
              disabled: false
            });

            modelEditor.setReadOnly(false);
          } else {
            parser = new DOMParser();
            new_graph_outer =
              parser.parseFromString(e.data.graph, "image/svg+xml").documentElement;
            new_graph_outer.setAttribute("width", "100%");
            new_graph_outer.setAttribute("height", "100%");
            new_graph_outer.setAttribute("id", "graph-outer");
            $("#graph-div").empty();
            $("#graph-div").append(new_graph_outer);

            my_zoom = d3.behavior.zoom()
              .scaleExtent([0.1, 10]).on("zoom", function() {
                zoom();
              });
            d3.select(document.getElementById("graph-outer")).call(my_zoom);

            original_transform = $("#graph0").attr("transform");
            translate_regex = /translate\((\-?\d*\.?\d*) (\-?\d*\.?\d*)\)/;
            original_translate = translate_regex.exec(original_transform);
            my_zoom.translate([original_translate[1], original_translate[2]]);
            //restoreGraph();

            logAppend("Done!  See graph below\n");
            $("#graphbutton").button({
              disabled: false
            }).click(restoreGraph);
            $("#run-button").button({
              disabled: false
            });

            modelEditor.setReadOnly(false);
          }
        }

        grapher.postMessage(e.data.result.graph);
      } else {
        result.value = "(no graph)\n";
        logAppend("Not Observable\n");
        $("#run-button").button({
          disabled: false
        });
        modelEditor.setReadOnly(false);
      }
    } else if (e.data.type == "ltparseerror") {
        result.value = "(no graph)\n";
        logAppend("Litmus test parsing error, line " + e.data.row +
            ", column " + e.data.col + "\n");
        testEditor.setValue(restored);
        testEditor.clearSelection();
        testEditor.gotoLine(e.data.row, e.data.col, true);
        resetAll(false);
    } else if (e.data.type == "modelparseerror") {
        result.value = "(no graph)\n";
        logAppend("(Micro)architecture parsing error, line " + e.data.row +
            ", column " + e.data.col + "\n");
        modelEditor.gotoLine(e.data.row, e.data.col, true);
        resetAll(false);
    } else if (e.data.type == "error") {
        result.value = "(no graph)\n";
        logAppend("Error!\n");
        logAppend(e.data.name + "\n");
        logAppend(e.data.message + "\n");
    } else {
        result.value = "(no graph)\n";
        logAppend("Not Observable\n");
        console.log("Unknown message type!");
    }
  }

  worker.postMessage({
    "model": modelEditor.getValue(),
    "test": testEditor.getValue()});
};

$(function() {
  availableModels = [
    "pipecheck/FiveStage.uarch",
    "pipecheck/gem5.uarch",
    "pipecheck/gem5-slrbug.uarch",
    "ccicheck/FiveStageTSOCC.uarch",
    "ccicheck/FiveStagePeekaboo.uarch",
  ];

  $("#modelselect").autocomplete({
    width: 300,
    source: availableModels,
    change: updateModel,
    select: function(event, ui) {
      this.value = ui.item.value;
      updateModel()
    },
    minLength: 0
  });
  $("#modelselect").val("pipecheck/FiveStage.uarch");
  modelModified = false;
  modelPrevious = "pipecheck/FiveStage.uarch";
  updateModel();

  $("#modelselect").bind("focus", function() {
    this.value = "";
    $(this).autocomplete("search", "");
  });

  availableTags = [
      "x86tso/amd10",
      "x86tso/amd3",
      "x86tso/amd5",
      "x86tso/co-iriw",
      "x86tso/co-mp",
      "x86tso/iriw",
      "x86tso/iwp23b",
      "x86tso/iwp24",
      "x86tso/iwp24a",
      "x86tso/iwp27",
      "x86tso/iwp28a",
      "x86tso/iwp28b",
      "x86tso/lb",
      "x86tso/mp+fences",
      "x86tso/mp",
      "x86tso/mp+staleld",
      "x86tso/n1",
      "x86tso/n2",
      "x86tso/n3",
      "x86tso/n4",
      "x86tso/n5",
      "x86tso/n6",
      "x86tso/n7",
      "x86tso/n8",
      "x86tso/podwr000",
      "x86tso/podwr001",
      "x86tso/rfi000",
      "x86tso/rfi001",
      "x86tso/rfi002",
      "x86tso/rfi003",
      "x86tso/rfi004",
      "x86tso/rfi005",
      "x86tso/rfi006",
      "x86tso/rfi007",
      "x86tso/rfi008",
      "x86tso/rfi009",
      "x86tso/rfi010",
      "x86tso/rfi011",
      "x86tso/rfi012",
      "x86tso/rfi013",
      "x86tso/rfi014",
      "x86tso/rfi015",
      "x86tso/rfi016",
      "x86tso/rfi017",
      "x86tso/rfi018",
      "x86tso/rwc-fenced",
      "x86tso/rwc-unfenced",
      "x86tso/safe000",
      "x86tso/safe001",
      "x86tso/safe002",
      "x86tso/safe003",
      "x86tso/safe004",
      "x86tso/safe005",
      "x86tso/safe006",
      "x86tso/safe007",
      "x86tso/safe008",
      "x86tso/safe009",
      "x86tso/safe010",
      "x86tso/safe011",
      "x86tso/safe012",
      "x86tso/safe013",
      "x86tso/safe014",
      "x86tso/safe015",
      "x86tso/safe016",
      "x86tso/safe017",
      "x86tso/safe018",
      "x86tso/safe019",
      "x86tso/safe020",
      "x86tso/safe021",
      "x86tso/safe022",
      "x86tso/safe023",
      "x86tso/safe024",
      "x86tso/safe025",
      "x86tso/safe026",
      "x86tso/safe027",
      "x86tso/safe028",
      "x86tso/safe029",
      "x86tso/safe030",
      "x86tso/safe031",
      "x86tso/safe032",
      "x86tso/safe033",
      "x86tso/safe034",
      "x86tso/safe035",
      "x86tso/safe036",
      "x86tso/safe037",
      "x86tso/sb",
      "x86tso/ssl",
      "x86tso/testandset2",
      "x86tso/testandset+earlyld",
      "x86tso/testandset",
      "x86tso/wrc+dep",
      "x86tso/wrc"
    ];

  $("#testselect").autocomplete({
    source: function(request, response) {
      var limit = 50;
      if (request.term == "") {
        if (availableTags.length > limit) {
          response(availableTags.slice(0, limit));
          $("#maxtests").text("(first " + limit + " results shown)");
        } else {
          response(availableTags);
          $("#maxtests").text("");
        }
      } else {
        var results = $.ui.autocomplete.filter(availableTags, request.term);
        if (results.length > limit) {
          response(results.slice(0, limit));
          $("#maxtests").text("(first " + limit + " results shown)");
        } else {
          response(results);
          $("#maxtests").text("");
        }
      }
    },
    change: updateTest,
    select: function(event, ui) {
      this.value = ui.item.value;
      updateTest();
    },
    minLength: 0
  });

  $("#testselect").bind("focus", function() {
    this.value = "";
    $(this).autocomplete("search", "");
  });

  $("#testselect").val("x86tso/sb");
  updateTest();

});

function zoom() {
  d3.select(document.getElementById("graph0"))
    .attr("transform", "translate(" + my_zoom.translate() + ")" +
        "scale(" + my_zoom.scale() + ")");
}

