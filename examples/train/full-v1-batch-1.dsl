package railway {
  enum Position {
    FAILURE;
    STRAIGHT;
    DIVERGING;
  }
  enum Signal {
    FAILURE;
    STOP;
    GO;
  }
  abstract class RailwayElement {
    id : Integer [0..1] ordered nonunique;
  }
  class RailwayContainer {
    routes : railway::Route [0..*] ordered unique composite;
    regions : railway::Region [0..*] ordered unique composite;
  }
  class Region extends railway::RailwayElement {
    sensors : railway::Sensor [0..*] ordered unique composite;
    elements : railway::TrackElement [0..*] ordered unique composite;
  }
  class Route extends railway::RailwayElement {
    active : Boolean [0..1] ordered nonunique;
    follows : railway::SwitchPosition [0..*] ordered unique composite;
    requires : railway::Sensor [2..*] ordered unique;
    entry : railway::Semaphore [0..1] ordered unique;
    exit : railway::Semaphore [0..1] ordered unique;
  }
  class Sensor extends railway::RailwayElement {
    monitors : railway::TrackElement [0..*] ordered unique;
  }
  abstract class TrackElement extends railway::RailwayElement {
    monitoredBy : railway::Sensor [0..*] ordered unique;
    connectsTo : railway::TrackElement [0..*] ordered unique;
  }
  class Segment extends railway::TrackElement {
    length : Integer [0..1] ordered nonunique;
    semaphores : railway::Semaphore [0..*] ordered unique composite;
  }
  class Switch extends railway::TrackElement {
    currentPosition : enum railway::Position [0..1] ordered nonunique;
    positions : railway::SwitchPosition [0..*] ordered unique;
  }
  class SwitchPosition extends railway::RailwayElement {
    position : enum railway::Position [0..1] ordered nonunique;
    route : railway::Route [0..1] ordered unique;
    target : railway::Switch [0..1] ordered unique;
  }
  class Semaphore extends railway::RailwayElement {
    signal : enum railway::Signal [0..1] ordered nonunique;
  }
  association follows__route {
    ends railway::Route::follows, railway::SwitchPosition::route;
  }
  association monitors__monitoredBy {
    ends railway::Sensor::monitors, railway::TrackElement::monitoredBy;
  }
  association positions__target {
    ends railway::Switch::positions, railway::SwitchPosition::target;
  }
}

object o0 : railway::RailwayContainer {
  observe railway::RailwayContainer::routes = [@o1, @o3, @o6, @o11, @o13];
  observe railway::RailwayContainer::regions = [@o24, @o69, @o175, @o301, @o358];
}

object o1 : railway::Route {
  observe railway::RailwayElement::id = [3];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@o2];
  observe railway::Route::requires = [@o25, @o26, @o27, @o28, @o29, @o30, @o31];
  observe railway::Route::entry = [@o425];
  observe railway::Route::exit = [@o34];
}

object o2 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [48];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o1];
  observe railway::SwitchPosition::target = [@o32];
}

object o3 : railway::Route {
  observe railway::RailwayElement::id = [50];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@o4, @o5];
  observe railway::Route::requires = [@o70, @o71, @o72, @o73, @o74, @o75, @o76, @o77, @o78, @o79, @o80, @o81, @o82, @o83, @o84, @o85, @o86];
  observe railway::Route::entry = [@o34];
  observe railway::Route::exit = [@o89];
}

object o4 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [101];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@o3];
  observe railway::SwitchPosition::target = [@o87];
}

object o5 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [157];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o3];
  observe railway::SwitchPosition::target = [@o129];
}

object o6 : railway::Route {
  observe railway::RailwayElement::id = [159];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@o7, @o8, @o9, @o10];
  observe railway::Route::requires = [@o176, @o177, @o178, @o179, @o180, @o181, @o182, @o183, @o184, @o185, @o186, @o187, @o188, @o189, @o190, @o191, @o192, @o193, @o194, @o195];
  observe railway::Route::entry = [@o89];
  observe railway::Route::exit = [@o198];
}

object o7 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [186];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o6];
  observe railway::SwitchPosition::target = [@o196];
}

object o8 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [218];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@o6];
  observe railway::SwitchPosition::target = [@o218];
}

object o9 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [238];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o6];
  observe railway::SwitchPosition::target = [@o244];
}

object o10 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [288];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o6];
  observe railway::SwitchPosition::target = [@o260];
}

object o11 : railway::Route {
  observe railway::RailwayElement::id = [290];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@o12];
  observe railway::Route::requires = [@o302, @o303, @o304, @o305, @o306, @o307, @o308, @o309, @o310];
  observe railway::Route::entry = [@o198];
  observe railway::Route::exit = [@o313];
}

object o12 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [347];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o11];
  observe railway::SwitchPosition::target = [@o311];
}

object o13 : railway::Route {
  observe railway::RailwayElement::id = [348];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@o14, @o15, @o16, @o17, @o18, @o19, @o20, @o21, @o22, @o23];
  observe railway::Route::requires = [@o359, @o360, @o361, @o362, @o363, @o364, @o365, @o366, @o367, @o368, @o369, @o370, @o371, @o372, @o373, @o374, @o375, @o376, @o377, @o378, @o379, @o380, @o381, @o382, @o383, @o384, @o385, @o386, @o387, @o388, @o389, @o390, @o391, @o392, @o393, @o394, @o395, @o396, @o397, @o398, @o399, @o400, @o401, @o402, @o403, @o404, @o405, @o406, @o407, @o408, @o409, @o410, @o411, @o412, @o413, @o414, @o415, @o416, @o417, @o418, @o419, @o420, @o421, @o422];
  observe railway::Route::entry = [@o313];
  observe railway::Route::exit = [@o425];
}

object o14 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [405];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o423];
}

object o15 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [461];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o470];
}

object o16 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [469];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o516];
}

object o17 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [525];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o522];
}

object o18 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [581];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o568];
}

object o19 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [613];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o614];
}

object o20 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [621];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o640];
}

object o21 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [677];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o646];
}

object o22 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [721];
  observe railway::SwitchPosition::position = [railway::Position::DIVERGING];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o692];
}

object o23 : railway::SwitchPosition {
  observe railway::RailwayElement::id = [753];
  observe railway::SwitchPosition::position = [];
  observe railway::SwitchPosition::route = [@o13];
  observe railway::SwitchPosition::target = [@o728];
}

object o24 : railway::Region {
  observe railway::RailwayElement::id = [4];
  observe railway::Region::sensors = [@o25, @o26, @o27, @o28, @o29, @o30, @o31];
  observe railway::Region::elements = [@o32, @o33, @o35, @o36, @o37, @o38, @o39, @o40, @o41, @o42, @o43, @o44, @o45, @o46, @o47, @o48, @o49, @o50, @o51, @o52, @o53, @o54, @o55, @o56, @o57, @o58, @o59, @o60, @o61, @o62, @o63, @o64, @o65, @o66, @o67, @o68];
}

object o25 : railway::Sensor {
  observe railway::RailwayElement::id = [6];
  observe railway::Sensor::monitors = [@o32, @o33, @o35, @o36, @o37, @o38];
}

object o26 : railway::Sensor {
  observe railway::RailwayElement::id = [12];
  observe railway::Sensor::monitors = [@o32, @o39, @o40, @o41, @o42, @o43];
}

object o27 : railway::Sensor {
  observe railway::RailwayElement::id = [18];
  observe railway::Sensor::monitors = [@o32, @o44, @o45, @o46, @o47, @o48];
}

object o28 : railway::Sensor {
  observe railway::RailwayElement::id = [24];
  observe railway::Sensor::monitors = [@o32, @o49, @o50, @o51, @o52, @o53];
}

object o29 : railway::Sensor {
  observe railway::RailwayElement::id = [30];
  observe railway::Sensor::monitors = [@o32, @o54, @o55, @o56, @o57, @o58];
}

object o30 : railway::Sensor {
  observe railway::RailwayElement::id = [36];
  observe railway::Sensor::monitors = [@o32, @o59, @o60, @o61, @o62, @o63];
}

object o31 : railway::Sensor {
  observe railway::RailwayElement::id = [42];
  observe railway::Sensor::monitors = [@o32, @o64, @o65, @o66, @o67, @o68];
}

object o32 : railway::Switch {
  observe railway::RailwayElement::id = [5];
  observe railway::TrackElement::monitoredBy = [@o25, @o26, @o27, @o28, @o29, @o30, @o31];
  observe railway::TrackElement::connectsTo = [@o33];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o2];
}

object o33 : railway::Segment {
  observe railway::RailwayElement::id = [7];
  observe railway::TrackElement::monitoredBy = [@o25];
  observe railway::TrackElement::connectsTo = [@o35];
  observe railway::Segment::length = [335];
  observe railway::Segment::semaphores = [@o34];
}

object o34 : railway::Semaphore {
  observe railway::RailwayElement::id = [2];
  observe railway::Semaphore::signal = [railway::Signal::GO];
}

object o35 : railway::Segment {
  observe railway::RailwayElement::id = [8];
  observe railway::TrackElement::monitoredBy = [@o25];
  observe railway::TrackElement::connectsTo = [@o36];
  observe railway::Segment::length = [439];
  observe railway::Segment::semaphores = [];
}

object o36 : railway::Segment {
  observe railway::RailwayElement::id = [9];
  observe railway::TrackElement::monitoredBy = [@o25];
  observe railway::TrackElement::connectsTo = [@o37];
  observe railway::Segment::length = [90];
  observe railway::Segment::semaphores = [];
}

object o37 : railway::Segment {
  observe railway::RailwayElement::id = [10];
  observe railway::TrackElement::monitoredBy = [@o25];
  observe railway::TrackElement::connectsTo = [@o38];
  observe railway::Segment::length = [395];
  observe railway::Segment::semaphores = [];
}

object o38 : railway::Segment {
  observe railway::RailwayElement::id = [11];
  observe railway::TrackElement::monitoredBy = [@o25];
  observe railway::TrackElement::connectsTo = [@o39];
  observe railway::Segment::length = [134];
  observe railway::Segment::semaphores = [];
}

object o39 : railway::Segment {
  observe railway::RailwayElement::id = [13];
  observe railway::TrackElement::monitoredBy = [@o26];
  observe railway::TrackElement::connectsTo = [@o40];
  observe railway::Segment::length = [137];
  observe railway::Segment::semaphores = [];
}

object o40 : railway::Segment {
  observe railway::RailwayElement::id = [14];
  observe railway::TrackElement::monitoredBy = [@o26];
  observe railway::TrackElement::connectsTo = [@o41];
  observe railway::Segment::length = [494];
  observe railway::Segment::semaphores = [];
}

object o41 : railway::Segment {
  observe railway::RailwayElement::id = [15];
  observe railway::TrackElement::monitoredBy = [@o26];
  observe railway::TrackElement::connectsTo = [@o42];
  observe railway::Segment::length = [979];
  observe railway::Segment::semaphores = [];
}

object o42 : railway::Segment {
  observe railway::RailwayElement::id = [16];
  observe railway::TrackElement::monitoredBy = [@o26];
  observe railway::TrackElement::connectsTo = [@o43];
  observe railway::Segment::length = [815];
  observe railway::Segment::semaphores = [];
}

object o43 : railway::Segment {
  observe railway::RailwayElement::id = [17];
  observe railway::TrackElement::monitoredBy = [@o26];
  observe railway::TrackElement::connectsTo = [@o44];
  observe railway::Segment::length = [813];
  observe railway::Segment::semaphores = [];
}

object o44 : railway::Segment {
  observe railway::RailwayElement::id = [19];
  observe railway::TrackElement::monitoredBy = [@o27];
  observe railway::TrackElement::connectsTo = [@o45];
  observe railway::Segment::length = [968];
  observe railway::Segment::semaphores = [];
}

object o45 : railway::Segment {
  observe railway::RailwayElement::id = [20];
  observe railway::TrackElement::monitoredBy = [@o27];
  observe railway::TrackElement::connectsTo = [@o46];
  observe railway::Segment::length = [197];
  observe railway::Segment::semaphores = [];
}

object o46 : railway::Segment {
  observe railway::RailwayElement::id = [21];
  observe railway::TrackElement::monitoredBy = [@o27];
  observe railway::TrackElement::connectsTo = [@o47];
  observe railway::Segment::length = [324];
  observe railway::Segment::semaphores = [];
}

object o47 : railway::Segment {
  observe railway::RailwayElement::id = [22];
  observe railway::TrackElement::monitoredBy = [@o27];
  observe railway::TrackElement::connectsTo = [@o48];
  observe railway::Segment::length = [645];
  observe railway::Segment::semaphores = [];
}

object o48 : railway::Segment {
  observe railway::RailwayElement::id = [23];
  observe railway::TrackElement::monitoredBy = [@o27];
  observe railway::TrackElement::connectsTo = [@o49];
  observe railway::Segment::length = [517];
  observe railway::Segment::semaphores = [];
}

object o49 : railway::Segment {
  observe railway::RailwayElement::id = [25];
  observe railway::TrackElement::monitoredBy = [@o28];
  observe railway::TrackElement::connectsTo = [@o50];
  observe railway::Segment::length = [212];
  observe railway::Segment::semaphores = [];
}

object o50 : railway::Segment {
  observe railway::RailwayElement::id = [26];
  observe railway::TrackElement::monitoredBy = [@o28];
  observe railway::TrackElement::connectsTo = [@o51];
  observe railway::Segment::length = [994];
  observe railway::Segment::semaphores = [];
}

object o51 : railway::Segment {
  observe railway::RailwayElement::id = [27];
  observe railway::TrackElement::monitoredBy = [@o28];
  observe railway::TrackElement::connectsTo = [@o52];
  observe railway::Segment::length = [472];
  observe railway::Segment::semaphores = [];
}

object o52 : railway::Segment {
  observe railway::RailwayElement::id = [28];
  observe railway::TrackElement::monitoredBy = [@o28];
  observe railway::TrackElement::connectsTo = [@o53];
  observe railway::Segment::length = [679];
  observe railway::Segment::semaphores = [];
}

object o53 : railway::Segment {
  observe railway::RailwayElement::id = [29];
  observe railway::TrackElement::monitoredBy = [@o28];
  observe railway::TrackElement::connectsTo = [@o54];
  observe railway::Segment::length = [745];
  observe railway::Segment::semaphores = [];
}

object o54 : railway::Segment {
  observe railway::RailwayElement::id = [31];
  observe railway::TrackElement::monitoredBy = [@o29];
  observe railway::TrackElement::connectsTo = [@o55];
  observe railway::Segment::length = [542];
  observe railway::Segment::semaphores = [];
}

object o55 : railway::Segment {
  observe railway::RailwayElement::id = [32];
  observe railway::TrackElement::monitoredBy = [@o29];
  observe railway::TrackElement::connectsTo = [@o56];
  observe railway::Segment::length = [655];
  observe railway::Segment::semaphores = [];
}

object o56 : railway::Segment {
  observe railway::RailwayElement::id = [33];
  observe railway::TrackElement::monitoredBy = [@o29];
  observe railway::TrackElement::connectsTo = [@o57];
  observe railway::Segment::length = [988];
  observe railway::Segment::semaphores = [];
}

object o57 : railway::Segment {
  observe railway::RailwayElement::id = [34];
  observe railway::TrackElement::monitoredBy = [@o29];
  observe railway::TrackElement::connectsTo = [@o58];
  observe railway::Segment::length = [483];
  observe railway::Segment::semaphores = [];
}

object o58 : railway::Segment {
  observe railway::RailwayElement::id = [35];
  observe railway::TrackElement::monitoredBy = [@o29];
  observe railway::TrackElement::connectsTo = [@o59];
  observe railway::Segment::length = [636];
  observe railway::Segment::semaphores = [];
}

object o59 : railway::Segment {
  observe railway::RailwayElement::id = [37];
  observe railway::TrackElement::monitoredBy = [@o30];
  observe railway::TrackElement::connectsTo = [@o60];
  observe railway::Segment::length = [429];
  observe railway::Segment::semaphores = [];
}

object o60 : railway::Segment {
  observe railway::RailwayElement::id = [38];
  observe railway::TrackElement::monitoredBy = [@o30];
  observe railway::TrackElement::connectsTo = [@o61];
  observe railway::Segment::length = [892];
  observe railway::Segment::semaphores = [];
}

object o61 : railway::Segment {
  observe railway::RailwayElement::id = [39];
  observe railway::TrackElement::monitoredBy = [@o30];
  observe railway::TrackElement::connectsTo = [@o62];
  observe railway::Segment::length = [149];
  observe railway::Segment::semaphores = [];
}

object o62 : railway::Segment {
  observe railway::RailwayElement::id = [40];
  observe railway::TrackElement::monitoredBy = [@o30];
  observe railway::TrackElement::connectsTo = [@o63];
  observe railway::Segment::length = [209];
  observe railway::Segment::semaphores = [];
}

object o63 : railway::Segment {
  observe railway::RailwayElement::id = [41];
  observe railway::TrackElement::monitoredBy = [@o30];
  observe railway::TrackElement::connectsTo = [@o64];
  observe railway::Segment::length = [721];
  observe railway::Segment::semaphores = [];
}

object o64 : railway::Segment {
  observe railway::RailwayElement::id = [43];
  observe railway::TrackElement::monitoredBy = [@o31];
  observe railway::TrackElement::connectsTo = [@o65];
  observe railway::Segment::length = [853];
  observe railway::Segment::semaphores = [];
}

object o65 : railway::Segment {
  observe railway::RailwayElement::id = [44];
  observe railway::TrackElement::monitoredBy = [@o31];
  observe railway::TrackElement::connectsTo = [@o66];
  observe railway::Segment::length = [560];
  observe railway::Segment::semaphores = [];
}

object o66 : railway::Segment {
  observe railway::RailwayElement::id = [45];
  observe railway::TrackElement::monitoredBy = [@o31];
  observe railway::TrackElement::connectsTo = [@o67];
  observe railway::Segment::length = [190];
  observe railway::Segment::semaphores = [];
}

object o67 : railway::Segment {
  observe railway::RailwayElement::id = [46];
  observe railway::TrackElement::monitoredBy = [@o31];
  observe railway::TrackElement::connectsTo = [@o68];
  observe railway::Segment::length = [764];
  observe railway::Segment::semaphores = [];
}

object o68 : railway::Segment {
  observe railway::RailwayElement::id = [47];
  observe railway::TrackElement::monitoredBy = [@o31];
  observe railway::TrackElement::connectsTo = [@o87];
  observe railway::Segment::length = [872];
  observe railway::Segment::semaphores = [];
}

object o69 : railway::Region {
  observe railway::RailwayElement::id = [51];
  observe railway::Region::sensors = [@o70, @o71, @o72, @o73, @o74, @o75, @o76, @o77, @o78, @o79, @o80, @o81, @o82, @o83, @o84, @o85, @o86];
  observe railway::Region::elements = [@o87, @o88, @o90, @o91, @o92, @o93, @o94, @o95, @o96, @o97, @o98, @o99, @o100, @o101, @o102, @o103, @o104, @o105, @o106, @o107, @o108, @o109, @o110, @o111, @o112, @o113, @o114, @o115, @o116, @o117, @o118, @o119, @o120, @o121, @o122, @o123, @o124, @o125, @o126, @o127, @o128, @o129, @o130, @o131, @o132, @o133, @o134, @o135, @o136, @o137, @o138, @o139, @o140, @o141, @o142, @o143, @o144, @o145, @o146, @o147, @o148, @o149, @o150, @o151, @o152, @o153, @o154, @o155, @o156, @o157, @o158, @o159, @o160, @o161, @o162, @o163, @o164, @o165, @o166, @o167, @o168, @o169, @o170, @o171, @o172, @o173, @o174];
}

object o70 : railway::Sensor {
  observe railway::RailwayElement::id = [53];
  observe railway::Sensor::monitors = [@o87, @o88, @o90, @o91, @o92, @o93];
}

object o71 : railway::Sensor {
  observe railway::RailwayElement::id = [59];
  observe railway::Sensor::monitors = [@o87, @o94, @o95, @o96, @o97, @o98];
}

object o72 : railway::Sensor {
  observe railway::RailwayElement::id = [65];
  observe railway::Sensor::monitors = [@o87, @o99, @o100, @o101, @o102, @o103];
}

object o73 : railway::Sensor {
  observe railway::RailwayElement::id = [71];
  observe railway::Sensor::monitors = [@o87, @o104, @o105, @o106, @o107, @o108];
}

object o74 : railway::Sensor {
  observe railway::RailwayElement::id = [77];
  observe railway::Sensor::monitors = [@o87, @o109, @o110, @o111, @o112, @o113];
}

object o75 : railway::Sensor {
  observe railway::RailwayElement::id = [83];
  observe railway::Sensor::monitors = [@o87, @o114, @o115, @o116, @o117, @o118];
}

object o76 : railway::Sensor {
  observe railway::RailwayElement::id = [89];
  observe railway::Sensor::monitors = [@o87, @o119, @o120, @o121, @o122, @o123];
}

object o77 : railway::Sensor {
  observe railway::RailwayElement::id = [95];
  observe railway::Sensor::monitors = [@o87, @o124, @o125, @o126, @o127, @o128];
}

object o78 : railway::Sensor {
  observe railway::RailwayElement::id = [103];
  observe railway::Sensor::monitors = [@o129, @o130, @o131, @o132, @o133, @o134];
}

object o79 : railway::Sensor {
  observe railway::RailwayElement::id = [109];
  observe railway::Sensor::monitors = [@o129, @o135, @o136, @o137, @o138, @o139];
}

object o80 : railway::Sensor {
  observe railway::RailwayElement::id = [115];
  observe railway::Sensor::monitors = [@o129, @o140, @o141, @o142, @o143, @o144];
}

object o81 : railway::Sensor {
  observe railway::RailwayElement::id = [121];
  observe railway::Sensor::monitors = [@o129, @o145, @o146, @o147, @o148, @o149];
}

object o82 : railway::Sensor {
  observe railway::RailwayElement::id = [127];
  observe railway::Sensor::monitors = [@o129, @o150, @o151, @o152, @o153, @o154];
}

object o83 : railway::Sensor {
  observe railway::RailwayElement::id = [133];
  observe railway::Sensor::monitors = [@o129, @o155, @o156, @o157, @o158, @o159];
}

object o84 : railway::Sensor {
  observe railway::RailwayElement::id = [139];
  observe railway::Sensor::monitors = [@o129, @o160, @o161, @o162, @o163, @o164];
}

object o85 : railway::Sensor {
  observe railway::RailwayElement::id = [145];
  observe railway::Sensor::monitors = [@o129, @o165, @o166, @o167, @o168, @o169];
}

object o86 : railway::Sensor {
  observe railway::RailwayElement::id = [151];
  observe railway::Sensor::monitors = [@o129, @o170, @o171, @o172, @o173, @o174];
}

object o87 : railway::Switch {
  observe railway::RailwayElement::id = [52];
  observe railway::TrackElement::monitoredBy = [@o70, @o71, @o72, @o73, @o74, @o75, @o76, @o77];
  observe railway::TrackElement::connectsTo = [@o88];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@o4];
}

object o88 : railway::Segment {
  observe railway::RailwayElement::id = [54];
  observe railway::TrackElement::monitoredBy = [@o70];
  observe railway::TrackElement::connectsTo = [@o90];
  observe railway::Segment::length = [232];
  observe railway::Segment::semaphores = [@o89];
}

object o89 : railway::Semaphore {
  observe railway::RailwayElement::id = [49];
  observe railway::Semaphore::signal = [railway::Signal::GO];
}

object o90 : railway::Segment {
  observe railway::RailwayElement::id = [55];
  observe railway::TrackElement::monitoredBy = [@o70];
  observe railway::TrackElement::connectsTo = [@o91];
  observe railway::Segment::length = [901];
  observe railway::Segment::semaphores = [];
}

object o91 : railway::Segment {
  observe railway::RailwayElement::id = [56];
  observe railway::TrackElement::monitoredBy = [@o70];
  observe railway::TrackElement::connectsTo = [@o92];
  observe railway::Segment::length = [530];
  observe railway::Segment::semaphores = [];
}

object o92 : railway::Segment {
  observe railway::RailwayElement::id = [57];
  observe railway::TrackElement::monitoredBy = [@o70];
  observe railway::TrackElement::connectsTo = [@o93];
  observe railway::Segment::length = [494];
  observe railway::Segment::semaphores = [];
}

object o93 : railway::Segment {
  observe railway::RailwayElement::id = [58];
  observe railway::TrackElement::monitoredBy = [@o70];
  observe railway::TrackElement::connectsTo = [@o94];
  observe railway::Segment::length = [273];
  observe railway::Segment::semaphores = [];
}

object o94 : railway::Segment {
  observe railway::RailwayElement::id = [60];
  observe railway::TrackElement::monitoredBy = [@o71];
  observe railway::TrackElement::connectsTo = [@o95];
  observe railway::Segment::length = [975];
  observe railway::Segment::semaphores = [];
}

object o95 : railway::Segment {
  observe railway::RailwayElement::id = [61];
  observe railway::TrackElement::monitoredBy = [@o71];
  observe railway::TrackElement::connectsTo = [@o96];
  observe railway::Segment::length = [386];
  observe railway::Segment::semaphores = [];
}

object o96 : railway::Segment {
  observe railway::RailwayElement::id = [62];
  observe railway::TrackElement::monitoredBy = [@o71];
  observe railway::TrackElement::connectsTo = [@o97];
  observe railway::Segment::length = [220];
  observe railway::Segment::semaphores = [];
}

object o97 : railway::Segment {
  observe railway::RailwayElement::id = [63];
  observe railway::TrackElement::monitoredBy = [@o71];
  observe railway::TrackElement::connectsTo = [@o98];
  observe railway::Segment::length = [929];
  observe railway::Segment::semaphores = [];
}

object o98 : railway::Segment {
  observe railway::RailwayElement::id = [64];
  observe railway::TrackElement::monitoredBy = [@o71];
  observe railway::TrackElement::connectsTo = [@o99];
  observe railway::Segment::length = [152];
  observe railway::Segment::semaphores = [];
}

object o99 : railway::Segment {
  observe railway::RailwayElement::id = [66];
  observe railway::TrackElement::monitoredBy = [@o72];
  observe railway::TrackElement::connectsTo = [@o100];
  observe railway::Segment::length = [246];
  observe railway::Segment::semaphores = [];
}

object o100 : railway::Segment {
  observe railway::RailwayElement::id = [67];
  observe railway::TrackElement::monitoredBy = [@o72];
  observe railway::TrackElement::connectsTo = [@o101];
  observe railway::Segment::length = [246];
  observe railway::Segment::semaphores = [];
}

object o101 : railway::Segment {
  observe railway::RailwayElement::id = [68];
  observe railway::TrackElement::monitoredBy = [@o72];
  observe railway::TrackElement::connectsTo = [@o102];
  observe railway::Segment::length = [437];
  observe railway::Segment::semaphores = [];
}

object o102 : railway::Segment {
  observe railway::RailwayElement::id = [69];
  observe railway::TrackElement::monitoredBy = [@o72];
  observe railway::TrackElement::connectsTo = [@o103];
  observe railway::Segment::length = [375];
  observe railway::Segment::semaphores = [];
}

object o103 : railway::Segment {
  observe railway::RailwayElement::id = [70];
  observe railway::TrackElement::monitoredBy = [@o72];
  observe railway::TrackElement::connectsTo = [@o104];
  observe railway::Segment::length = [942];
  observe railway::Segment::semaphores = [];
}

object o104 : railway::Segment {
  observe railway::RailwayElement::id = [72];
  observe railway::TrackElement::monitoredBy = [@o73];
  observe railway::TrackElement::connectsTo = [@o105];
  observe railway::Segment::length = [301];
  observe railway::Segment::semaphores = [];
}

object o105 : railway::Segment {
  observe railway::RailwayElement::id = [73];
  observe railway::TrackElement::monitoredBy = [@o73];
  observe railway::TrackElement::connectsTo = [@o106];
  observe railway::Segment::length = [437];
  observe railway::Segment::semaphores = [];
}

object o106 : railway::Segment {
  observe railway::RailwayElement::id = [74];
  observe railway::TrackElement::monitoredBy = [@o73];
  observe railway::TrackElement::connectsTo = [@o107];
  observe railway::Segment::length = [511];
  observe railway::Segment::semaphores = [];
}

object o107 : railway::Segment {
  observe railway::RailwayElement::id = [75];
  observe railway::TrackElement::monitoredBy = [@o73];
  observe railway::TrackElement::connectsTo = [@o108];
  observe railway::Segment::length = [625];
  observe railway::Segment::semaphores = [];
}

object o108 : railway::Segment {
  observe railway::RailwayElement::id = [76];
  observe railway::TrackElement::monitoredBy = [@o73];
  observe railway::TrackElement::connectsTo = [@o109];
  observe railway::Segment::length = [111];
  observe railway::Segment::semaphores = [];
}

object o109 : railway::Segment {
  observe railway::RailwayElement::id = [78];
  observe railway::TrackElement::monitoredBy = [@o74];
  observe railway::TrackElement::connectsTo = [@o110];
  observe railway::Segment::length = [227];
  observe railway::Segment::semaphores = [];
}

object o110 : railway::Segment {
  observe railway::RailwayElement::id = [79];
  observe railway::TrackElement::monitoredBy = [@o74];
  observe railway::TrackElement::connectsTo = [@o111];
  observe railway::Segment::length = [145];
  observe railway::Segment::semaphores = [];
}

object o111 : railway::Segment {
  observe railway::RailwayElement::id = [80];
  observe railway::TrackElement::monitoredBy = [@o74];
  observe railway::TrackElement::connectsTo = [@o112];
  observe railway::Segment::length = [789];
  observe railway::Segment::semaphores = [];
}

object o112 : railway::Segment {
  observe railway::RailwayElement::id = [81];
  observe railway::TrackElement::monitoredBy = [@o74];
  observe railway::TrackElement::connectsTo = [@o113];
  observe railway::Segment::length = [456];
  observe railway::Segment::semaphores = [];
}

object o113 : railway::Segment {
  observe railway::RailwayElement::id = [82];
  observe railway::TrackElement::monitoredBy = [@o74];
  observe railway::TrackElement::connectsTo = [@o114];
  observe railway::Segment::length = [434];
  observe railway::Segment::semaphores = [];
}

object o114 : railway::Segment {
  observe railway::RailwayElement::id = [84];
  observe railway::TrackElement::monitoredBy = [@o75];
  observe railway::TrackElement::connectsTo = [@o115];
  observe railway::Segment::length = [824];
  observe railway::Segment::semaphores = [];
}

object o115 : railway::Segment {
  observe railway::RailwayElement::id = [85];
  observe railway::TrackElement::monitoredBy = [@o75];
  observe railway::TrackElement::connectsTo = [@o116];
  observe railway::Segment::length = [395];
  observe railway::Segment::semaphores = [];
}

object o116 : railway::Segment {
  observe railway::RailwayElement::id = [86];
  observe railway::TrackElement::monitoredBy = [@o75];
  observe railway::TrackElement::connectsTo = [@o117];
  observe railway::Segment::length = [608];
  observe railway::Segment::semaphores = [];
}

object o117 : railway::Segment {
  observe railway::RailwayElement::id = [87];
  observe railway::TrackElement::monitoredBy = [@o75];
  observe railway::TrackElement::connectsTo = [@o118];
  observe railway::Segment::length = [829];
  observe railway::Segment::semaphores = [];
}

object o118 : railway::Segment {
  observe railway::RailwayElement::id = [88];
  observe railway::TrackElement::monitoredBy = [@o75];
  observe railway::TrackElement::connectsTo = [@o119];
  observe railway::Segment::length = [619];
  observe railway::Segment::semaphores = [];
}

object o119 : railway::Segment {
  observe railway::RailwayElement::id = [90];
  observe railway::TrackElement::monitoredBy = [@o76];
  observe railway::TrackElement::connectsTo = [@o120];
  observe railway::Segment::length = [921];
  observe railway::Segment::semaphores = [];
}

object o120 : railway::Segment {
  observe railway::RailwayElement::id = [91];
  observe railway::TrackElement::monitoredBy = [@o76];
  observe railway::TrackElement::connectsTo = [@o121];
  observe railway::Segment::length = [329];
  observe railway::Segment::semaphores = [];
}

object o121 : railway::Segment {
  observe railway::RailwayElement::id = [92];
  observe railway::TrackElement::monitoredBy = [@o76];
  observe railway::TrackElement::connectsTo = [@o122];
  observe railway::Segment::length = [703];
  observe railway::Segment::semaphores = [];
}

object o122 : railway::Segment {
  observe railway::RailwayElement::id = [93];
  observe railway::TrackElement::monitoredBy = [@o76];
  observe railway::TrackElement::connectsTo = [@o123];
  observe railway::Segment::length = [763];
  observe railway::Segment::semaphores = [];
}

object o123 : railway::Segment {
  observe railway::RailwayElement::id = [94];
  observe railway::TrackElement::monitoredBy = [@o76];
  observe railway::TrackElement::connectsTo = [@o124];
  observe railway::Segment::length = [890];
  observe railway::Segment::semaphores = [];
}

object o124 : railway::Segment {
  observe railway::RailwayElement::id = [96];
  observe railway::TrackElement::monitoredBy = [@o77];
  observe railway::TrackElement::connectsTo = [@o125];
  observe railway::Segment::length = [257];
  observe railway::Segment::semaphores = [];
}

object o125 : railway::Segment {
  observe railway::RailwayElement::id = [97];
  observe railway::TrackElement::monitoredBy = [@o77];
  observe railway::TrackElement::connectsTo = [@o126];
  observe railway::Segment::length = [488];
  observe railway::Segment::semaphores = [];
}

object o126 : railway::Segment {
  observe railway::RailwayElement::id = [98];
  observe railway::TrackElement::monitoredBy = [@o77];
  observe railway::TrackElement::connectsTo = [@o127];
  observe railway::Segment::length = [366];
  observe railway::Segment::semaphores = [];
}

object o127 : railway::Segment {
  observe railway::RailwayElement::id = [99];
  observe railway::TrackElement::monitoredBy = [@o77];
  observe railway::TrackElement::connectsTo = [@o128];
  observe railway::Segment::length = [638];
  observe railway::Segment::semaphores = [];
}

object o128 : railway::Segment {
  observe railway::RailwayElement::id = [100];
  observe railway::TrackElement::monitoredBy = [@o77];
  observe railway::TrackElement::connectsTo = [@o129];
  observe railway::Segment::length = [102];
  observe railway::Segment::semaphores = [];
}

object o129 : railway::Switch {
  observe railway::RailwayElement::id = [102];
  observe railway::TrackElement::monitoredBy = [@o78, @o79, @o80, @o81, @o82, @o83, @o84, @o85, @o86];
  observe railway::TrackElement::connectsTo = [@o130];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o5];
}

object o130 : railway::Segment {
  observe railway::RailwayElement::id = [104];
  observe railway::TrackElement::monitoredBy = [@o78];
  observe railway::TrackElement::connectsTo = [@o131];
  observe railway::Segment::length = [386];
  observe railway::Segment::semaphores = [];
}

object o131 : railway::Segment {
  observe railway::RailwayElement::id = [105];
  observe railway::TrackElement::monitoredBy = [@o78];
  observe railway::TrackElement::connectsTo = [@o132];
  observe railway::Segment::length = [462];
  observe railway::Segment::semaphores = [];
}

object o132 : railway::Segment {
  observe railway::RailwayElement::id = [106];
  observe railway::TrackElement::monitoredBy = [@o78];
  observe railway::TrackElement::connectsTo = [@o133];
  observe railway::Segment::length = [657];
  observe railway::Segment::semaphores = [];
}

object o133 : railway::Segment {
  observe railway::RailwayElement::id = [107];
  observe railway::TrackElement::monitoredBy = [@o78];
  observe railway::TrackElement::connectsTo = [@o134];
  observe railway::Segment::length = [931];
  observe railway::Segment::semaphores = [];
}

object o134 : railway::Segment {
  observe railway::RailwayElement::id = [108];
  observe railway::TrackElement::monitoredBy = [@o78];
  observe railway::TrackElement::connectsTo = [@o135];
  observe railway::Segment::length = [119];
  observe railway::Segment::semaphores = [];
}

object o135 : railway::Segment {
  observe railway::RailwayElement::id = [110];
  observe railway::TrackElement::monitoredBy = [@o79];
  observe railway::TrackElement::connectsTo = [@o136];
  observe railway::Segment::length = [392];
  observe railway::Segment::semaphores = [];
}

object o136 : railway::Segment {
  observe railway::RailwayElement::id = [111];
  observe railway::TrackElement::monitoredBy = [@o79];
  observe railway::TrackElement::connectsTo = [@o137];
  observe railway::Segment::length = [782];
  observe railway::Segment::semaphores = [];
}

object o137 : railway::Segment {
  observe railway::RailwayElement::id = [112];
  observe railway::TrackElement::monitoredBy = [@o79];
  observe railway::TrackElement::connectsTo = [@o138];
  observe railway::Segment::length = [212];
  observe railway::Segment::semaphores = [];
}

object o138 : railway::Segment {
  observe railway::RailwayElement::id = [113];
  observe railway::TrackElement::monitoredBy = [@o79];
  observe railway::TrackElement::connectsTo = [@o139];
  observe railway::Segment::length = [907];
  observe railway::Segment::semaphores = [];
}

object o139 : railway::Segment {
  observe railway::RailwayElement::id = [114];
  observe railway::TrackElement::monitoredBy = [@o79];
  observe railway::TrackElement::connectsTo = [@o140];
  observe railway::Segment::length = [118];
  observe railway::Segment::semaphores = [];
}

object o140 : railway::Segment {
  observe railway::RailwayElement::id = [116];
  observe railway::TrackElement::monitoredBy = [@o80];
  observe railway::TrackElement::connectsTo = [@o141];
  observe railway::Segment::length = [186];
  observe railway::Segment::semaphores = [];
}

object o141 : railway::Segment {
  observe railway::RailwayElement::id = [117];
  observe railway::TrackElement::monitoredBy = [@o80];
  observe railway::TrackElement::connectsTo = [@o142];
  observe railway::Segment::length = [324];
  observe railway::Segment::semaphores = [];
}

object o142 : railway::Segment {
  observe railway::RailwayElement::id = [118];
  observe railway::TrackElement::monitoredBy = [@o80];
  observe railway::TrackElement::connectsTo = [@o143];
  observe railway::Segment::length = [881];
  observe railway::Segment::semaphores = [];
}

object o143 : railway::Segment {
  observe railway::RailwayElement::id = [119];
  observe railway::TrackElement::monitoredBy = [@o80];
  observe railway::TrackElement::connectsTo = [@o144];
  observe railway::Segment::length = [740];
  observe railway::Segment::semaphores = [];
}

object o144 : railway::Segment {
  observe railway::RailwayElement::id = [120];
  observe railway::TrackElement::monitoredBy = [@o80];
  observe railway::TrackElement::connectsTo = [@o145];
  observe railway::Segment::length = [897];
  observe railway::Segment::semaphores = [];
}

object o145 : railway::Segment {
  observe railway::RailwayElement::id = [122];
  observe railway::TrackElement::monitoredBy = [@o81];
  observe railway::TrackElement::connectsTo = [@o146];
  observe railway::Segment::length = [250];
  observe railway::Segment::semaphores = [];
}

object o146 : railway::Segment {
  observe railway::RailwayElement::id = [123];
  observe railway::TrackElement::monitoredBy = [@o81];
  observe railway::TrackElement::connectsTo = [@o147];
  observe railway::Segment::length = [579];
  observe railway::Segment::semaphores = [];
}

object o147 : railway::Segment {
  observe railway::RailwayElement::id = [124];
  observe railway::TrackElement::monitoredBy = [@o81];
  observe railway::TrackElement::connectsTo = [@o148];
  observe railway::Segment::length = [39];
  observe railway::Segment::semaphores = [];
}

object o148 : railway::Segment {
  observe railway::RailwayElement::id = [125];
  observe railway::TrackElement::monitoredBy = [@o81];
  observe railway::TrackElement::connectsTo = [@o149];
  observe railway::Segment::length = [91];
  observe railway::Segment::semaphores = [];
}

object o149 : railway::Segment {
  observe railway::RailwayElement::id = [126];
  observe railway::TrackElement::monitoredBy = [@o81];
  observe railway::TrackElement::connectsTo = [@o150];
  observe railway::Segment::length = [963];
  observe railway::Segment::semaphores = [];
}

object o150 : railway::Segment {
  observe railway::RailwayElement::id = [128];
  observe railway::TrackElement::monitoredBy = [@o82];
  observe railway::TrackElement::connectsTo = [@o151];
  observe railway::Segment::length = [718];
  observe railway::Segment::semaphores = [];
}

object o151 : railway::Segment {
  observe railway::RailwayElement::id = [129];
  observe railway::TrackElement::monitoredBy = [@o82];
  observe railway::TrackElement::connectsTo = [@o152];
  observe railway::Segment::length = [942];
  observe railway::Segment::semaphores = [];
}

object o152 : railway::Segment {
  observe railway::RailwayElement::id = [130];
  observe railway::TrackElement::monitoredBy = [@o82];
  observe railway::TrackElement::connectsTo = [@o153];
  observe railway::Segment::length = [547];
  observe railway::Segment::semaphores = [];
}

object o153 : railway::Segment {
  observe railway::RailwayElement::id = [131];
  observe railway::TrackElement::monitoredBy = [@o82];
  observe railway::TrackElement::connectsTo = [@o154];
  observe railway::Segment::length = [836];
  observe railway::Segment::semaphores = [];
}

object o154 : railway::Segment {
  observe railway::RailwayElement::id = [132];
  observe railway::TrackElement::monitoredBy = [@o82];
  observe railway::TrackElement::connectsTo = [@o155];
  observe railway::Segment::length = [579];
  observe railway::Segment::semaphores = [];
}

object o155 : railway::Segment {
  observe railway::RailwayElement::id = [134];
  observe railway::TrackElement::monitoredBy = [@o83];
  observe railway::TrackElement::connectsTo = [@o156];
  observe railway::Segment::length = [870];
  observe railway::Segment::semaphores = [];
}

object o156 : railway::Segment {
  observe railway::RailwayElement::id = [135];
  observe railway::TrackElement::monitoredBy = [@o83];
  observe railway::TrackElement::connectsTo = [@o157];
  observe railway::Segment::length = [344];
  observe railway::Segment::semaphores = [];
}

object o157 : railway::Segment {
  observe railway::RailwayElement::id = [136];
  observe railway::TrackElement::monitoredBy = [@o83];
  observe railway::TrackElement::connectsTo = [@o158];
  observe railway::Segment::length = [333];
  observe railway::Segment::semaphores = [];
}

object o158 : railway::Segment {
  observe railway::RailwayElement::id = [137];
  observe railway::TrackElement::monitoredBy = [@o83];
  observe railway::TrackElement::connectsTo = [@o159];
  observe railway::Segment::length = [923];
  observe railway::Segment::semaphores = [];
}

object o159 : railway::Segment {
  observe railway::RailwayElement::id = [138];
  observe railway::TrackElement::monitoredBy = [@o83];
  observe railway::TrackElement::connectsTo = [@o160];
  observe railway::Segment::length = [627];
  observe railway::Segment::semaphores = [];
}

object o160 : railway::Segment {
  observe railway::RailwayElement::id = [140];
  observe railway::TrackElement::monitoredBy = [@o84];
  observe railway::TrackElement::connectsTo = [@o161];
  observe railway::Segment::length = [465];
  observe railway::Segment::semaphores = [];
}

object o161 : railway::Segment {
  observe railway::RailwayElement::id = [141];
  observe railway::TrackElement::monitoredBy = [@o84];
  observe railway::TrackElement::connectsTo = [@o162];
  observe railway::Segment::length = [470];
  observe railway::Segment::semaphores = [];
}

object o162 : railway::Segment {
  observe railway::RailwayElement::id = [142];
  observe railway::TrackElement::monitoredBy = [@o84];
  observe railway::TrackElement::connectsTo = [@o163];
  observe railway::Segment::length = [343];
  observe railway::Segment::semaphores = [];
}

object o163 : railway::Segment {
  observe railway::RailwayElement::id = [143];
  observe railway::TrackElement::monitoredBy = [@o84];
  observe railway::TrackElement::connectsTo = [@o164];
  observe railway::Segment::length = [771];
  observe railway::Segment::semaphores = [];
}

object o164 : railway::Segment {
  observe railway::RailwayElement::id = [144];
  observe railway::TrackElement::monitoredBy = [@o84];
  observe railway::TrackElement::connectsTo = [@o165];
  observe railway::Segment::length = [288];
  observe railway::Segment::semaphores = [];
}

object o165 : railway::Segment {
  observe railway::RailwayElement::id = [146];
  observe railway::TrackElement::monitoredBy = [@o85];
  observe railway::TrackElement::connectsTo = [@o166];
  observe railway::Segment::length = [167];
  observe railway::Segment::semaphores = [];
}

object o166 : railway::Segment {
  observe railway::RailwayElement::id = [147];
  observe railway::TrackElement::monitoredBy = [@o85];
  observe railway::TrackElement::connectsTo = [@o167];
  observe railway::Segment::length = [466];
  observe railway::Segment::semaphores = [];
}

object o167 : railway::Segment {
  observe railway::RailwayElement::id = [148];
  observe railway::TrackElement::monitoredBy = [@o85];
  observe railway::TrackElement::connectsTo = [@o168];
  observe railway::Segment::length = [886];
  observe railway::Segment::semaphores = [];
}

object o168 : railway::Segment {
  observe railway::RailwayElement::id = [149];
  observe railway::TrackElement::monitoredBy = [@o85];
  observe railway::TrackElement::connectsTo = [@o169];
  observe railway::Segment::length = [248];
  observe railway::Segment::semaphores = [];
}

object o169 : railway::Segment {
  observe railway::RailwayElement::id = [150];
  observe railway::TrackElement::monitoredBy = [@o85];
  observe railway::TrackElement::connectsTo = [@o170];
  observe railway::Segment::length = [261];
  observe railway::Segment::semaphores = [];
}

object o170 : railway::Segment {
  observe railway::RailwayElement::id = [152];
  observe railway::TrackElement::monitoredBy = [@o86];
  observe railway::TrackElement::connectsTo = [@o171];
  observe railway::Segment::length = [36];
  observe railway::Segment::semaphores = [];
}

object o171 : railway::Segment {
  observe railway::RailwayElement::id = [153];
  observe railway::TrackElement::monitoredBy = [@o86];
  observe railway::TrackElement::connectsTo = [@o172];
  observe railway::Segment::length = [458];
  observe railway::Segment::semaphores = [];
}

object o172 : railway::Segment {
  observe railway::RailwayElement::id = [154];
  observe railway::TrackElement::monitoredBy = [@o86];
  observe railway::TrackElement::connectsTo = [@o173];
  observe railway::Segment::length = [918];
  observe railway::Segment::semaphores = [];
}

object o173 : railway::Segment {
  observe railway::RailwayElement::id = [155];
  observe railway::TrackElement::monitoredBy = [@o86];
  observe railway::TrackElement::connectsTo = [@o174];
  observe railway::Segment::length = [345];
  observe railway::Segment::semaphores = [];
}

object o174 : railway::Segment {
  observe railway::RailwayElement::id = [156];
  observe railway::TrackElement::monitoredBy = [@o86];
  observe railway::TrackElement::connectsTo = [@o196];
  observe railway::Segment::length = [820];
  observe railway::Segment::semaphores = [];
}

object o175 : railway::Region {
  observe railway::RailwayElement::id = [160];
  observe railway::Region::sensors = [@o176, @o177, @o178, @o179, @o180, @o181, @o182, @o183, @o184, @o185, @o186, @o187, @o188, @o189, @o190, @o191, @o192, @o193, @o194, @o195];
  observe railway::Region::elements = [@o196, @o197, @o199, @o200, @o201, @o202, @o203, @o204, @o205, @o206, @o207, @o208, @o209, @o210, @o211, @o212, @o213, @o214, @o215, @o216, @o217, @o218, @o219, @o220, @o221, @o222, @o223, @o224, @o225, @o226, @o227, @o228, @o229, @o230, @o231, @o232, @o233, @o234, @o235, @o236, @o237, @o238, @o239, @o240, @o241, @o242, @o243, @o244, @o245, @o246, @o247, @o248, @o249, @o250, @o251, @o252, @o253, @o254, @o255, @o256, @o257, @o258, @o259, @o260, @o261, @o262, @o263, @o264, @o265, @o266, @o267, @o268, @o269, @o270, @o271, @o272, @o273, @o274, @o275, @o276, @o277, @o278, @o279, @o280, @o281, @o282, @o283, @o284, @o285, @o286, @o287, @o288, @o289, @o290, @o291, @o292, @o293, @o294, @o295, @o296, @o297, @o298, @o299, @o300];
}

object o176 : railway::Sensor {
  observe railway::RailwayElement::id = [162];
  observe railway::Sensor::monitors = [@o196, @o197, @o199, @o200, @o201, @o202];
}

object o177 : railway::Sensor {
  observe railway::RailwayElement::id = [168];
  observe railway::Sensor::monitors = [@o196, @o203, @o204, @o205, @o206, @o207];
}

object o178 : railway::Sensor {
  observe railway::RailwayElement::id = [174];
  observe railway::Sensor::monitors = [@o196, @o208, @o209, @o210, @o211, @o212];
}

object o179 : railway::Sensor {
  observe railway::RailwayElement::id = [180];
  observe railway::Sensor::monitors = [@o196, @o213, @o214, @o215, @o216, @o217];
}

object o180 : railway::Sensor {
  observe railway::RailwayElement::id = [188];
  observe railway::Sensor::monitors = [@o218, @o219, @o220, @o221, @o222, @o223];
}

object o181 : railway::Sensor {
  observe railway::RailwayElement::id = [194];
  observe railway::Sensor::monitors = [@o218, @o224, @o225, @o226, @o227, @o228];
}

object o182 : railway::Sensor {
  observe railway::RailwayElement::id = [200];
  observe railway::Sensor::monitors = [@o218, @o229, @o230, @o231, @o232, @o233];
}

object o183 : railway::Sensor {
  observe railway::RailwayElement::id = [206];
  observe railway::Sensor::monitors = [@o218, @o234, @o235, @o236, @o237, @o238];
}

object o184 : railway::Sensor {
  observe railway::RailwayElement::id = [212];
  observe railway::Sensor::monitors = [@o218, @o239, @o240, @o241, @o242, @o243];
}

object o185 : railway::Sensor {
  observe railway::RailwayElement::id = [220];
  observe railway::Sensor::monitors = [@o244, @o245, @o246, @o247, @o248, @o249];
}

object o186 : railway::Sensor {
  observe railway::RailwayElement::id = [226];
  observe railway::Sensor::monitors = [@o244, @o250, @o251, @o252, @o253, @o254];
}

object o187 : railway::Sensor {
  observe railway::RailwayElement::id = [232];
  observe railway::Sensor::monitors = [@o244, @o255, @o256, @o257, @o258, @o259];
}

object o188 : railway::Sensor {
  observe railway::RailwayElement::id = [240];
  observe railway::Sensor::monitors = [@o260, @o261, @o262, @o263, @o264, @o265];
}

object o189 : railway::Sensor {
  observe railway::RailwayElement::id = [246];
  observe railway::Sensor::monitors = [@o260, @o266, @o267, @o268, @o269, @o270];
}

object o190 : railway::Sensor {
  observe railway::RailwayElement::id = [252];
  observe railway::Sensor::monitors = [@o260, @o271, @o272, @o273, @o274, @o275];
}

object o191 : railway::Sensor {
  observe railway::RailwayElement::id = [258];
  observe railway::Sensor::monitors = [@o260, @o276, @o277, @o278, @o279, @o280];
}

object o192 : railway::Sensor {
  observe railway::RailwayElement::id = [264];
  observe railway::Sensor::monitors = [@o260, @o281, @o282, @o283, @o284, @o285];
}

object o193 : railway::Sensor {
  observe railway::RailwayElement::id = [270];
  observe railway::Sensor::monitors = [@o260, @o286, @o287, @o288, @o289, @o290];
}

object o194 : railway::Sensor {
  observe railway::RailwayElement::id = [276];
  observe railway::Sensor::monitors = [@o260, @o291, @o292, @o293, @o294, @o295];
}

object o195 : railway::Sensor {
  observe railway::RailwayElement::id = [282];
  observe railway::Sensor::monitors = [@o260, @o296, @o297, @o298, @o299, @o300];
}

object o196 : railway::Switch {
  observe railway::RailwayElement::id = [161];
  observe railway::TrackElement::monitoredBy = [@o176, @o177, @o178, @o179];
  observe railway::TrackElement::connectsTo = [@o197];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o7];
}

object o197 : railway::Segment {
  observe railway::RailwayElement::id = [163];
  observe railway::TrackElement::monitoredBy = [@o176];
  observe railway::TrackElement::connectsTo = [@o199];
  observe railway::Segment::length = [369];
  observe railway::Segment::semaphores = [@o198];
}

object o198 : railway::Semaphore {
  observe railway::RailwayElement::id = [158];
  observe railway::Semaphore::signal = [railway::Signal::GO];
}

object o199 : railway::Segment {
  observe railway::RailwayElement::id = [164];
  observe railway::TrackElement::monitoredBy = [@o176];
  observe railway::TrackElement::connectsTo = [@o200];
  observe railway::Segment::length = [94];
  observe railway::Segment::semaphores = [];
}

object o200 : railway::Segment {
  observe railway::RailwayElement::id = [165];
  observe railway::TrackElement::monitoredBy = [@o176];
  observe railway::TrackElement::connectsTo = [@o201];
  observe railway::Segment::length = [737];
  observe railway::Segment::semaphores = [];
}

object o201 : railway::Segment {
  observe railway::RailwayElement::id = [166];
  observe railway::TrackElement::monitoredBy = [@o176];
  observe railway::TrackElement::connectsTo = [@o202];
  observe railway::Segment::length = [433];
  observe railway::Segment::semaphores = [];
}

object o202 : railway::Segment {
  observe railway::RailwayElement::id = [167];
  observe railway::TrackElement::monitoredBy = [@o176];
  observe railway::TrackElement::connectsTo = [@o203];
  observe railway::Segment::length = [149];
  observe railway::Segment::semaphores = [];
}

object o203 : railway::Segment {
  observe railway::RailwayElement::id = [169];
  observe railway::TrackElement::monitoredBy = [@o177];
  observe railway::TrackElement::connectsTo = [@o204];
  observe railway::Segment::length = [70];
  observe railway::Segment::semaphores = [];
}

object o204 : railway::Segment {
  observe railway::RailwayElement::id = [170];
  observe railway::TrackElement::monitoredBy = [@o177];
  observe railway::TrackElement::connectsTo = [@o205];
  observe railway::Segment::length = [809];
  observe railway::Segment::semaphores = [];
}

object o205 : railway::Segment {
  observe railway::RailwayElement::id = [171];
  observe railway::TrackElement::monitoredBy = [@o177];
  observe railway::TrackElement::connectsTo = [@o206];
  observe railway::Segment::length = [160];
  observe railway::Segment::semaphores = [];
}

object o206 : railway::Segment {
  observe railway::RailwayElement::id = [172];
  observe railway::TrackElement::monitoredBy = [@o177];
  observe railway::TrackElement::connectsTo = [@o207];
  observe railway::Segment::length = [744];
  observe railway::Segment::semaphores = [];
}

object o207 : railway::Segment {
  observe railway::RailwayElement::id = [173];
  observe railway::TrackElement::monitoredBy = [@o177];
  observe railway::TrackElement::connectsTo = [@o208];
  observe railway::Segment::length = [461];
  observe railway::Segment::semaphores = [];
}

object o208 : railway::Segment {
  observe railway::RailwayElement::id = [175];
  observe railway::TrackElement::monitoredBy = [@o178];
  observe railway::TrackElement::connectsTo = [@o209];
  observe railway::Segment::length = [94];
  observe railway::Segment::semaphores = [];
}

object o209 : railway::Segment {
  observe railway::RailwayElement::id = [176];
  observe railway::TrackElement::monitoredBy = [@o178];
  observe railway::TrackElement::connectsTo = [@o210];
  observe railway::Segment::length = [627];
  observe railway::Segment::semaphores = [];
}

object o210 : railway::Segment {
  observe railway::RailwayElement::id = [177];
  observe railway::TrackElement::monitoredBy = [@o178];
  observe railway::TrackElement::connectsTo = [@o211];
  observe railway::Segment::length = [773];
  observe railway::Segment::semaphores = [];
}

object o211 : railway::Segment {
  observe railway::RailwayElement::id = [178];
  observe railway::TrackElement::monitoredBy = [@o178];
  observe railway::TrackElement::connectsTo = [@o212];
  observe railway::Segment::length = [493];
  observe railway::Segment::semaphores = [];
}

object o212 : railway::Segment {
  observe railway::RailwayElement::id = [179];
  observe railway::TrackElement::monitoredBy = [@o178];
  observe railway::TrackElement::connectsTo = [@o213];
  observe railway::Segment::length = [273];
  observe railway::Segment::semaphores = [];
}

object o213 : railway::Segment {
  observe railway::RailwayElement::id = [181];
  observe railway::TrackElement::monitoredBy = [@o179];
  observe railway::TrackElement::connectsTo = [@o214];
  observe railway::Segment::length = [157];
  observe railway::Segment::semaphores = [];
}

object o214 : railway::Segment {
  observe railway::RailwayElement::id = [182];
  observe railway::TrackElement::monitoredBy = [@o179];
  observe railway::TrackElement::connectsTo = [@o215];
  observe railway::Segment::length = [620];
  observe railway::Segment::semaphores = [];
}

object o215 : railway::Segment {
  observe railway::RailwayElement::id = [183];
  observe railway::TrackElement::monitoredBy = [@o179];
  observe railway::TrackElement::connectsTo = [@o216];
  observe railway::Segment::length = [905];
  observe railway::Segment::semaphores = [];
}

object o216 : railway::Segment {
  observe railway::RailwayElement::id = [184];
  observe railway::TrackElement::monitoredBy = [@o179];
  observe railway::TrackElement::connectsTo = [@o217];
  observe railway::Segment::length = [453];
  observe railway::Segment::semaphores = [];
}

object o217 : railway::Segment {
  observe railway::RailwayElement::id = [185];
  observe railway::TrackElement::monitoredBy = [@o179];
  observe railway::TrackElement::connectsTo = [@o218];
  observe railway::Segment::length = [322];
  observe railway::Segment::semaphores = [];
}

object o218 : railway::Switch {
  observe railway::RailwayElement::id = [187];
  observe railway::TrackElement::monitoredBy = [@o180, @o181, @o182, @o183, @o184];
  observe railway::TrackElement::connectsTo = [@o219];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@o8];
}

object o219 : railway::Segment {
  observe railway::RailwayElement::id = [189];
  observe railway::TrackElement::monitoredBy = [@o180];
  observe railway::TrackElement::connectsTo = [@o220];
  observe railway::Segment::length = [263];
  observe railway::Segment::semaphores = [];
}

object o220 : railway::Segment {
  observe railway::RailwayElement::id = [190];
  observe railway::TrackElement::monitoredBy = [@o180];
  observe railway::TrackElement::connectsTo = [@o221];
  observe railway::Segment::length = [970];
  observe railway::Segment::semaphores = [];
}

object o221 : railway::Segment {
  observe railway::RailwayElement::id = [191];
  observe railway::TrackElement::monitoredBy = [@o180];
  observe railway::TrackElement::connectsTo = [@o222];
  observe railway::Segment::length = [39];
  observe railway::Segment::semaphores = [];
}

object o222 : railway::Segment {
  observe railway::RailwayElement::id = [192];
  observe railway::TrackElement::monitoredBy = [@o180];
  observe railway::TrackElement::connectsTo = [@o223];
  observe railway::Segment::length = [83];
  observe railway::Segment::semaphores = [];
}

object o223 : railway::Segment {
  observe railway::RailwayElement::id = [193];
  observe railway::TrackElement::monitoredBy = [@o180];
  observe railway::TrackElement::connectsTo = [@o224];
  observe railway::Segment::length = [632];
  observe railway::Segment::semaphores = [];
}

object o224 : railway::Segment {
  observe railway::RailwayElement::id = [195];
  observe railway::TrackElement::monitoredBy = [@o181];
  observe railway::TrackElement::connectsTo = [@o225];
  observe railway::Segment::length = [546];
  observe railway::Segment::semaphores = [];
}

object o225 : railway::Segment {
  observe railway::RailwayElement::id = [196];
  observe railway::TrackElement::monitoredBy = [@o181];
  observe railway::TrackElement::connectsTo = [@o226];
  observe railway::Segment::length = [352];
  observe railway::Segment::semaphores = [];
}

object o226 : railway::Segment {
  observe railway::RailwayElement::id = [197];
  observe railway::TrackElement::monitoredBy = [@o181];
  observe railway::TrackElement::connectsTo = [@o227];
  observe railway::Segment::length = [742];
  observe railway::Segment::semaphores = [];
}

object o227 : railway::Segment {
  observe railway::RailwayElement::id = [198];
  observe railway::TrackElement::monitoredBy = [@o181];
  observe railway::TrackElement::connectsTo = [@o228];
  observe railway::Segment::length = [177];
  observe railway::Segment::semaphores = [];
}

object o228 : railway::Segment {
  observe railway::RailwayElement::id = [199];
  observe railway::TrackElement::monitoredBy = [@o181];
  observe railway::TrackElement::connectsTo = [@o229];
  observe railway::Segment::length = [576];
  observe railway::Segment::semaphores = [];
}

object o229 : railway::Segment {
  observe railway::RailwayElement::id = [201];
  observe railway::TrackElement::monitoredBy = [@o182];
  observe railway::TrackElement::connectsTo = [@o230];
  observe railway::Segment::length = [781];
  observe railway::Segment::semaphores = [];
}

object o230 : railway::Segment {
  observe railway::RailwayElement::id = [202];
  observe railway::TrackElement::monitoredBy = [@o182];
  observe railway::TrackElement::connectsTo = [@o231];
  observe railway::Segment::length = [83];
  observe railway::Segment::semaphores = [];
}

object o231 : railway::Segment {
  observe railway::RailwayElement::id = [203];
  observe railway::TrackElement::monitoredBy = [@o182];
  observe railway::TrackElement::connectsTo = [@o232];
  observe railway::Segment::length = [973];
  observe railway::Segment::semaphores = [];
}

object o232 : railway::Segment {
  observe railway::RailwayElement::id = [204];
  observe railway::TrackElement::monitoredBy = [@o182];
  observe railway::TrackElement::connectsTo = [@o233];
  observe railway::Segment::length = [918];
  observe railway::Segment::semaphores = [];
}

object o233 : railway::Segment {
  observe railway::RailwayElement::id = [205];
  observe railway::TrackElement::monitoredBy = [@o182];
  observe railway::TrackElement::connectsTo = [@o234];
  observe railway::Segment::length = [185];
  observe railway::Segment::semaphores = [];
}

object o234 : railway::Segment {
  observe railway::RailwayElement::id = [207];
  observe railway::TrackElement::monitoredBy = [@o183];
  observe railway::TrackElement::connectsTo = [@o235];
  observe railway::Segment::length = [847];
  observe railway::Segment::semaphores = [];
}

object o235 : railway::Segment {
  observe railway::RailwayElement::id = [208];
  observe railway::TrackElement::monitoredBy = [@o183];
  observe railway::TrackElement::connectsTo = [@o236];
  observe railway::Segment::length = [121];
  observe railway::Segment::semaphores = [];
}

object o236 : railway::Segment {
  observe railway::RailwayElement::id = [209];
  observe railway::TrackElement::monitoredBy = [@o183];
  observe railway::TrackElement::connectsTo = [@o237];
  observe railway::Segment::length = [977];
  observe railway::Segment::semaphores = [];
}

object o237 : railway::Segment {
  observe railway::RailwayElement::id = [210];
  observe railway::TrackElement::monitoredBy = [@o183];
  observe railway::TrackElement::connectsTo = [@o238];
  observe railway::Segment::length = [130];
  observe railway::Segment::semaphores = [];
}

object o238 : railway::Segment {
  observe railway::RailwayElement::id = [211];
  observe railway::TrackElement::monitoredBy = [@o183];
  observe railway::TrackElement::connectsTo = [@o239];
  observe railway::Segment::length = [69];
  observe railway::Segment::semaphores = [];
}

object o239 : railway::Segment {
  observe railway::RailwayElement::id = [213];
  observe railway::TrackElement::monitoredBy = [@o184];
  observe railway::TrackElement::connectsTo = [@o240];
  observe railway::Segment::length = [423];
  observe railway::Segment::semaphores = [];
}

object o240 : railway::Segment {
  observe railway::RailwayElement::id = [214];
  observe railway::TrackElement::monitoredBy = [@o184];
  observe railway::TrackElement::connectsTo = [@o241];
  observe railway::Segment::length = [450];
  observe railway::Segment::semaphores = [];
}

object o241 : railway::Segment {
  observe railway::RailwayElement::id = [215];
  observe railway::TrackElement::monitoredBy = [@o184];
  observe railway::TrackElement::connectsTo = [@o242];
  observe railway::Segment::length = [372];
  observe railway::Segment::semaphores = [];
}

object o242 : railway::Segment {
  observe railway::RailwayElement::id = [216];
  observe railway::TrackElement::monitoredBy = [@o184];
  observe railway::TrackElement::connectsTo = [@o243];
  observe railway::Segment::length = [993];
  observe railway::Segment::semaphores = [];
}

object o243 : railway::Segment {
  observe railway::RailwayElement::id = [217];
  observe railway::TrackElement::monitoredBy = [@o184];
  observe railway::TrackElement::connectsTo = [@o244];
  observe railway::Segment::length = [455];
  observe railway::Segment::semaphores = [];
}

object o244 : railway::Switch {
  observe railway::RailwayElement::id = [219];
  observe railway::TrackElement::monitoredBy = [@o185, @o186, @o187];
  observe railway::TrackElement::connectsTo = [@o245];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o9];
}

object o245 : railway::Segment {
  observe railway::RailwayElement::id = [221];
  observe railway::TrackElement::monitoredBy = [@o185];
  observe railway::TrackElement::connectsTo = [@o246];
  observe railway::Segment::length = [176];
  observe railway::Segment::semaphores = [];
}

object o246 : railway::Segment {
  observe railway::RailwayElement::id = [222];
  observe railway::TrackElement::monitoredBy = [@o185];
  observe railway::TrackElement::connectsTo = [@o247];
  observe railway::Segment::length = [759];
  observe railway::Segment::semaphores = [];
}

object o247 : railway::Segment {
  observe railway::RailwayElement::id = [223];
  observe railway::TrackElement::monitoredBy = [@o185];
  observe railway::TrackElement::connectsTo = [@o248];
  observe railway::Segment::length = [61];
  observe railway::Segment::semaphores = [];
}

object o248 : railway::Segment {
  observe railway::RailwayElement::id = [224];
  observe railway::TrackElement::monitoredBy = [@o185];
  observe railway::TrackElement::connectsTo = [@o249];
  observe railway::Segment::length = [917];
  observe railway::Segment::semaphores = [];
}

object o249 : railway::Segment {
  observe railway::RailwayElement::id = [225];
  observe railway::TrackElement::monitoredBy = [@o185];
  observe railway::TrackElement::connectsTo = [@o250];
  observe railway::Segment::length = [569];
  observe railway::Segment::semaphores = [];
}

object o250 : railway::Segment {
  observe railway::RailwayElement::id = [227];
  observe railway::TrackElement::monitoredBy = [@o186];
  observe railway::TrackElement::connectsTo = [@o251];
  observe railway::Segment::length = [571];
  observe railway::Segment::semaphores = [];
}

object o251 : railway::Segment {
  observe railway::RailwayElement::id = [228];
  observe railway::TrackElement::monitoredBy = [@o186];
  observe railway::TrackElement::connectsTo = [@o252];
  observe railway::Segment::length = [787];
  observe railway::Segment::semaphores = [];
}

object o252 : railway::Segment {
  observe railway::RailwayElement::id = [229];
  observe railway::TrackElement::monitoredBy = [@o186];
  observe railway::TrackElement::connectsTo = [@o253];
  observe railway::Segment::length = [35];
  observe railway::Segment::semaphores = [];
}

object o253 : railway::Segment {
  observe railway::RailwayElement::id = [230];
  observe railway::TrackElement::monitoredBy = [@o186];
  observe railway::TrackElement::connectsTo = [@o254];
  observe railway::Segment::length = [718];
  observe railway::Segment::semaphores = [];
}

object o254 : railway::Segment {
  observe railway::RailwayElement::id = [231];
  observe railway::TrackElement::monitoredBy = [@o186];
  observe railway::TrackElement::connectsTo = [@o255];
  observe railway::Segment::length = [307];
  observe railway::Segment::semaphores = [];
}

object o255 : railway::Segment {
  observe railway::RailwayElement::id = [233];
  observe railway::TrackElement::monitoredBy = [@o187];
  observe railway::TrackElement::connectsTo = [@o256];
  observe railway::Segment::length = [686];
  observe railway::Segment::semaphores = [];
}

object o256 : railway::Segment {
  observe railway::RailwayElement::id = [234];
  observe railway::TrackElement::monitoredBy = [@o187];
  observe railway::TrackElement::connectsTo = [@o257];
  observe railway::Segment::length = [858];
  observe railway::Segment::semaphores = [];
}

object o257 : railway::Segment {
  observe railway::RailwayElement::id = [235];
  observe railway::TrackElement::monitoredBy = [@o187];
  observe railway::TrackElement::connectsTo = [@o258];
  observe railway::Segment::length = [909];
  observe railway::Segment::semaphores = [];
}

object o258 : railway::Segment {
  observe railway::RailwayElement::id = [236];
  observe railway::TrackElement::monitoredBy = [@o187];
  observe railway::TrackElement::connectsTo = [@o259];
  observe railway::Segment::length = [750];
  observe railway::Segment::semaphores = [];
}

object o259 : railway::Segment {
  observe railway::RailwayElement::id = [237];
  observe railway::TrackElement::monitoredBy = [@o187];
  observe railway::TrackElement::connectsTo = [@o260];
  observe railway::Segment::length = [200];
  observe railway::Segment::semaphores = [];
}

object o260 : railway::Switch {
  observe railway::RailwayElement::id = [239];
  observe railway::TrackElement::monitoredBy = [@o188, @o189, @o190, @o191, @o192, @o193, @o194, @o195];
  observe railway::TrackElement::connectsTo = [@o261];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o10];
}

object o261 : railway::Segment {
  observe railway::RailwayElement::id = [241];
  observe railway::TrackElement::monitoredBy = [@o188];
  observe railway::TrackElement::connectsTo = [@o262];
  observe railway::Segment::length = [943];
  observe railway::Segment::semaphores = [];
}

object o262 : railway::Segment {
  observe railway::RailwayElement::id = [242];
  observe railway::TrackElement::monitoredBy = [@o188];
  observe railway::TrackElement::connectsTo = [@o263];
  observe railway::Segment::length = [168];
  observe railway::Segment::semaphores = [];
}

object o263 : railway::Segment {
  observe railway::RailwayElement::id = [243];
  observe railway::TrackElement::monitoredBy = [@o188];
  observe railway::TrackElement::connectsTo = [@o264];
  observe railway::Segment::length = [432];
  observe railway::Segment::semaphores = [];
}

object o264 : railway::Segment {
  observe railway::RailwayElement::id = [244];
  observe railway::TrackElement::monitoredBy = [@o188];
  observe railway::TrackElement::connectsTo = [@o265];
  observe railway::Segment::length = [589];
  observe railway::Segment::semaphores = [];
}

object o265 : railway::Segment {
  observe railway::RailwayElement::id = [245];
  observe railway::TrackElement::monitoredBy = [@o188];
  observe railway::TrackElement::connectsTo = [@o266];
  observe railway::Segment::length = [533];
  observe railway::Segment::semaphores = [];
}

object o266 : railway::Segment {
  observe railway::RailwayElement::id = [247];
  observe railway::TrackElement::monitoredBy = [@o189];
  observe railway::TrackElement::connectsTo = [@o267];
  observe railway::Segment::length = [29];
  observe railway::Segment::semaphores = [];
}

object o267 : railway::Segment {
  observe railway::RailwayElement::id = [248];
  observe railway::TrackElement::monitoredBy = [@o189];
  observe railway::TrackElement::connectsTo = [@o268];
  observe railway::Segment::length = [320];
  observe railway::Segment::semaphores = [];
}

object o268 : railway::Segment {
  observe railway::RailwayElement::id = [249];
  observe railway::TrackElement::monitoredBy = [@o189];
  observe railway::TrackElement::connectsTo = [@o269];
  observe railway::Segment::length = [225];
  observe railway::Segment::semaphores = [];
}

object o269 : railway::Segment {
  observe railway::RailwayElement::id = [250];
  observe railway::TrackElement::monitoredBy = [@o189];
  observe railway::TrackElement::connectsTo = [@o270];
  observe railway::Segment::length = [966];
  observe railway::Segment::semaphores = [];
}

object o270 : railway::Segment {
  observe railway::RailwayElement::id = [251];
  observe railway::TrackElement::monitoredBy = [@o189];
  observe railway::TrackElement::connectsTo = [@o271];
  observe railway::Segment::length = [517];
  observe railway::Segment::semaphores = [];
}

object o271 : railway::Segment {
  observe railway::RailwayElement::id = [253];
  observe railway::TrackElement::monitoredBy = [@o190];
  observe railway::TrackElement::connectsTo = [@o272];
  observe railway::Segment::length = [53];
  observe railway::Segment::semaphores = [];
}

object o272 : railway::Segment {
  observe railway::RailwayElement::id = [254];
  observe railway::TrackElement::monitoredBy = [@o190];
  observe railway::TrackElement::connectsTo = [@o273];
  observe railway::Segment::length = [916];
  observe railway::Segment::semaphores = [];
}

object o273 : railway::Segment {
  observe railway::RailwayElement::id = [255];
  observe railway::TrackElement::monitoredBy = [@o190];
  observe railway::TrackElement::connectsTo = [@o274];
  observe railway::Segment::length = [182];
  observe railway::Segment::semaphores = [];
}

object o274 : railway::Segment {
  observe railway::RailwayElement::id = [256];
  observe railway::TrackElement::monitoredBy = [@o190];
  observe railway::TrackElement::connectsTo = [@o275];
  observe railway::Segment::length = [972];
  observe railway::Segment::semaphores = [];
}

object o275 : railway::Segment {
  observe railway::RailwayElement::id = [257];
  observe railway::TrackElement::monitoredBy = [@o190];
  observe railway::TrackElement::connectsTo = [@o276];
  observe railway::Segment::length = [349];
  observe railway::Segment::semaphores = [];
}

object o276 : railway::Segment {
  observe railway::RailwayElement::id = [259];
  observe railway::TrackElement::monitoredBy = [@o191];
  observe railway::TrackElement::connectsTo = [@o277];
  observe railway::Segment::length = [51];
  observe railway::Segment::semaphores = [];
}

object o277 : railway::Segment {
  observe railway::RailwayElement::id = [260];
  observe railway::TrackElement::monitoredBy = [@o191];
  observe railway::TrackElement::connectsTo = [@o278];
  observe railway::Segment::length = [332];
  observe railway::Segment::semaphores = [];
}

object o278 : railway::Segment {
  observe railway::RailwayElement::id = [261];
  observe railway::TrackElement::monitoredBy = [@o191];
  observe railway::TrackElement::connectsTo = [@o279];
  observe railway::Segment::length = [282];
  observe railway::Segment::semaphores = [];
}

object o279 : railway::Segment {
  observe railway::RailwayElement::id = [262];
  observe railway::TrackElement::monitoredBy = [@o191];
  observe railway::TrackElement::connectsTo = [@o280];
  observe railway::Segment::length = [983];
  observe railway::Segment::semaphores = [];
}

object o280 : railway::Segment {
  observe railway::RailwayElement::id = [263];
  observe railway::TrackElement::monitoredBy = [@o191];
  observe railway::TrackElement::connectsTo = [@o281];
  observe railway::Segment::length = [78];
  observe railway::Segment::semaphores = [];
}

object o281 : railway::Segment {
  observe railway::RailwayElement::id = [265];
  observe railway::TrackElement::monitoredBy = [@o192];
  observe railway::TrackElement::connectsTo = [@o282];
  observe railway::Segment::length = [596];
  observe railway::Segment::semaphores = [];
}

object o282 : railway::Segment {
  observe railway::RailwayElement::id = [266];
  observe railway::TrackElement::monitoredBy = [@o192];
  observe railway::TrackElement::connectsTo = [@o283];
  observe railway::Segment::length = [331];
  observe railway::Segment::semaphores = [];
}

object o283 : railway::Segment {
  observe railway::RailwayElement::id = [267];
  observe railway::TrackElement::monitoredBy = [@o192];
  observe railway::TrackElement::connectsTo = [@o284];
  observe railway::Segment::length = [500];
  observe railway::Segment::semaphores = [];
}

object o284 : railway::Segment {
  observe railway::RailwayElement::id = [268];
  observe railway::TrackElement::monitoredBy = [@o192];
  observe railway::TrackElement::connectsTo = [@o285];
  observe railway::Segment::length = [683];
  observe railway::Segment::semaphores = [];
}

object o285 : railway::Segment {
  observe railway::RailwayElement::id = [269];
  observe railway::TrackElement::monitoredBy = [@o192];
  observe railway::TrackElement::connectsTo = [@o286];
  observe railway::Segment::length = [633];
  observe railway::Segment::semaphores = [];
}

object o286 : railway::Segment {
  observe railway::RailwayElement::id = [271];
  observe railway::TrackElement::monitoredBy = [@o193];
  observe railway::TrackElement::connectsTo = [@o287];
  observe railway::Segment::length = [836];
  observe railway::Segment::semaphores = [];
}

object o287 : railway::Segment {
  observe railway::RailwayElement::id = [272];
  observe railway::TrackElement::monitoredBy = [@o193];
  observe railway::TrackElement::connectsTo = [@o288];
  observe railway::Segment::length = [120];
  observe railway::Segment::semaphores = [];
}

object o288 : railway::Segment {
  observe railway::RailwayElement::id = [273];
  observe railway::TrackElement::monitoredBy = [@o193];
  observe railway::TrackElement::connectsTo = [@o289];
  observe railway::Segment::length = [173];
  observe railway::Segment::semaphores = [];
}

object o289 : railway::Segment {
  observe railway::RailwayElement::id = [274];
  observe railway::TrackElement::monitoredBy = [@o193];
  observe railway::TrackElement::connectsTo = [@o290];
  observe railway::Segment::length = [638];
  observe railway::Segment::semaphores = [];
}

object o290 : railway::Segment {
  observe railway::RailwayElement::id = [275];
  observe railway::TrackElement::monitoredBy = [@o193];
  observe railway::TrackElement::connectsTo = [@o291];
  observe railway::Segment::length = [792];
  observe railway::Segment::semaphores = [];
}

object o291 : railway::Segment {
  observe railway::RailwayElement::id = [277];
  observe railway::TrackElement::monitoredBy = [@o194];
  observe railway::TrackElement::connectsTo = [@o292];
  observe railway::Segment::length = [997];
  observe railway::Segment::semaphores = [];
}

object o292 : railway::Segment {
  observe railway::RailwayElement::id = [278];
  observe railway::TrackElement::monitoredBy = [@o194];
  observe railway::TrackElement::connectsTo = [@o293];
  observe railway::Segment::length = [809];
  observe railway::Segment::semaphores = [];
}

object o293 : railway::Segment {
  observe railway::RailwayElement::id = [279];
  observe railway::TrackElement::monitoredBy = [@o194];
  observe railway::TrackElement::connectsTo = [@o294];
  observe railway::Segment::length = [373];
  observe railway::Segment::semaphores = [];
}

object o294 : railway::Segment {
  observe railway::RailwayElement::id = [280];
  observe railway::TrackElement::monitoredBy = [@o194];
  observe railway::TrackElement::connectsTo = [@o295];
  observe railway::Segment::length = [954];
  observe railway::Segment::semaphores = [];
}

object o295 : railway::Segment {
  observe railway::RailwayElement::id = [281];
  observe railway::TrackElement::monitoredBy = [@o194];
  observe railway::TrackElement::connectsTo = [@o296];
  observe railway::Segment::length = [554];
  observe railway::Segment::semaphores = [];
}

object o296 : railway::Segment {
  observe railway::RailwayElement::id = [283];
  observe railway::TrackElement::monitoredBy = [@o195];
  observe railway::TrackElement::connectsTo = [@o297];
  observe railway::Segment::length = [915];
  observe railway::Segment::semaphores = [];
}

object o297 : railway::Segment {
  observe railway::RailwayElement::id = [284];
  observe railway::TrackElement::monitoredBy = [@o195];
  observe railway::TrackElement::connectsTo = [@o298];
  observe railway::Segment::length = [303];
  observe railway::Segment::semaphores = [];
}

object o298 : railway::Segment {
  observe railway::RailwayElement::id = [285];
  observe railway::TrackElement::monitoredBy = [@o195];
  observe railway::TrackElement::connectsTo = [@o299];
  observe railway::Segment::length = [977];
  observe railway::Segment::semaphores = [];
}

object o299 : railway::Segment {
  observe railway::RailwayElement::id = [286];
  observe railway::TrackElement::monitoredBy = [@o195];
  observe railway::TrackElement::connectsTo = [@o300];
  observe railway::Segment::length = [730];
  observe railway::Segment::semaphores = [];
}

object o300 : railway::Segment {
  observe railway::RailwayElement::id = [287];
  observe railway::TrackElement::monitoredBy = [@o195];
  observe railway::TrackElement::connectsTo = [@o311];
  observe railway::Segment::length = [312];
  observe railway::Segment::semaphores = [];
}

object o301 : railway::Region {
  observe railway::RailwayElement::id = [291];
  observe railway::Region::sensors = [@o302, @o303, @o304, @o305, @o306, @o307, @o308, @o309, @o310];
  observe railway::Region::elements = [@o311, @o312, @o314, @o315, @o316, @o317, @o318, @o319, @o320, @o321, @o322, @o323, @o324, @o325, @o326, @o327, @o328, @o329, @o330, @o331, @o332, @o333, @o334, @o335, @o336, @o337, @o338, @o339, @o340, @o341, @o342, @o343, @o344, @o345, @o346, @o347, @o348, @o349, @o350, @o351, @o352, @o353, @o354, @o355, @o356, @o357];
}

object o302 : railway::Sensor {
  observe railway::RailwayElement::id = [293];
  observe railway::Sensor::monitors = [@o311, @o312, @o314, @o315, @o316, @o317];
}

object o303 : railway::Sensor {
  observe railway::RailwayElement::id = [299];
  observe railway::Sensor::monitors = [@o311, @o318, @o319, @o320, @o321, @o322];
}

object o304 : railway::Sensor {
  observe railway::RailwayElement::id = [305];
  observe railway::Sensor::monitors = [@o311, @o323, @o324, @o325, @o326, @o327];
}

object o305 : railway::Sensor {
  observe railway::RailwayElement::id = [311];
  observe railway::Sensor::monitors = [@o311, @o328, @o329, @o330, @o331, @o332];
}

object o306 : railway::Sensor {
  observe railway::RailwayElement::id = [317];
  observe railway::Sensor::monitors = [@o311, @o333, @o334, @o335, @o336, @o337];
}

object o307 : railway::Sensor {
  observe railway::RailwayElement::id = [323];
  observe railway::Sensor::monitors = [@o311, @o338, @o339, @o340, @o341, @o342];
}

object o308 : railway::Sensor {
  observe railway::RailwayElement::id = [329];
  observe railway::Sensor::monitors = [@o311, @o343, @o344, @o345, @o346, @o347];
}

object o309 : railway::Sensor {
  observe railway::RailwayElement::id = [335];
  observe railway::Sensor::monitors = [@o311, @o348, @o349, @o350, @o351, @o352];
}

object o310 : railway::Sensor {
  observe railway::RailwayElement::id = [341];
  observe railway::Sensor::monitors = [@o311, @o353, @o354, @o355, @o356, @o357];
}

object o311 : railway::Switch {
  observe railway::RailwayElement::id = [292];
  observe railway::TrackElement::monitoredBy = [@o302, @o303, @o304, @o305, @o306, @o307, @o308, @o309, @o310];
  observe railway::TrackElement::connectsTo = [@o312];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o12];
}

object o312 : railway::Segment {
  observe railway::RailwayElement::id = [294];
  observe railway::TrackElement::monitoredBy = [@o302];
  observe railway::TrackElement::connectsTo = [@o314];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [@o313];
}

object o313 : railway::Semaphore {
  observe railway::RailwayElement::id = [289];
  observe railway::Semaphore::signal = [railway::Signal::GO];
}

object o314 : railway::Segment {
  observe railway::RailwayElement::id = [295];
  observe railway::TrackElement::monitoredBy = [@o302];
  observe railway::TrackElement::connectsTo = [@o315];
  observe railway::Segment::length = [573];
  observe railway::Segment::semaphores = [];
}

object o315 : railway::Segment {
  observe railway::RailwayElement::id = [296];
  observe railway::TrackElement::monitoredBy = [@o302];
  observe railway::TrackElement::connectsTo = [@o316];
  observe railway::Segment::length = [294];
  observe railway::Segment::semaphores = [];
}

object o316 : railway::Segment {
  observe railway::RailwayElement::id = [297];
  observe railway::TrackElement::monitoredBy = [@o302];
  observe railway::TrackElement::connectsTo = [@o317];
  observe railway::Segment::length = [488];
  observe railway::Segment::semaphores = [];
}

object o317 : railway::Segment {
  observe railway::RailwayElement::id = [298];
  observe railway::TrackElement::monitoredBy = [@o302];
  observe railway::TrackElement::connectsTo = [@o318];
  observe railway::Segment::length = [861];
  observe railway::Segment::semaphores = [];
}

object o318 : railway::Segment {
  observe railway::RailwayElement::id = [300];
  observe railway::TrackElement::monitoredBy = [@o303];
  observe railway::TrackElement::connectsTo = [@o319];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [];
}

object o319 : railway::Segment {
  observe railway::RailwayElement::id = [301];
  observe railway::TrackElement::monitoredBy = [@o303];
  observe railway::TrackElement::connectsTo = [@o320];
  observe railway::Segment::length = [455];
  observe railway::Segment::semaphores = [];
}

object o320 : railway::Segment {
  observe railway::RailwayElement::id = [302];
  observe railway::TrackElement::monitoredBy = [@o303];
  observe railway::TrackElement::connectsTo = [@o321];
  observe railway::Segment::length = [915];
  observe railway::Segment::semaphores = [];
}

object o321 : railway::Segment {
  observe railway::RailwayElement::id = [303];
  observe railway::TrackElement::monitoredBy = [@o303];
  observe railway::TrackElement::connectsTo = [@o322];
  observe railway::Segment::length = [182];
  observe railway::Segment::semaphores = [];
}

object o322 : railway::Segment {
  observe railway::RailwayElement::id = [304];
  observe railway::TrackElement::monitoredBy = [@o303];
  observe railway::TrackElement::connectsTo = [@o323];
  observe railway::Segment::length = [22];
  observe railway::Segment::semaphores = [];
}

object o323 : railway::Segment {
  observe railway::RailwayElement::id = [306];
  observe railway::TrackElement::monitoredBy = [@o304];
  observe railway::TrackElement::connectsTo = [@o324];
  observe railway::Segment::length = [118];
  observe railway::Segment::semaphores = [];
}

object o324 : railway::Segment {
  observe railway::RailwayElement::id = [307];
  observe railway::TrackElement::monitoredBy = [@o304];
  observe railway::TrackElement::connectsTo = [@o325];
  observe railway::Segment::length = [707];
  observe railway::Segment::semaphores = [];
}

object o325 : railway::Segment {
  observe railway::RailwayElement::id = [308];
  observe railway::TrackElement::monitoredBy = [@o304];
  observe railway::TrackElement::connectsTo = [@o326];
  observe railway::Segment::length = [342];
  observe railway::Segment::semaphores = [];
}

object o326 : railway::Segment {
  observe railway::RailwayElement::id = [309];
  observe railway::TrackElement::monitoredBy = [@o304];
  observe railway::TrackElement::connectsTo = [@o327];
  observe railway::Segment::length = [501];
  observe railway::Segment::semaphores = [];
}

object o327 : railway::Segment {
  observe railway::RailwayElement::id = [310];
  observe railway::TrackElement::monitoredBy = [@o304];
  observe railway::TrackElement::connectsTo = [@o328];
  observe railway::Segment::length = [953];
  observe railway::Segment::semaphores = [];
}

object o328 : railway::Segment {
  observe railway::RailwayElement::id = [312];
  observe railway::TrackElement::monitoredBy = [@o305];
  observe railway::TrackElement::connectsTo = [@o329];
  observe railway::Segment::length = [827];
  observe railway::Segment::semaphores = [];
}

object o329 : railway::Segment {
  observe railway::RailwayElement::id = [313];
  observe railway::TrackElement::monitoredBy = [@o305];
  observe railway::TrackElement::connectsTo = [@o330];
  observe railway::Segment::length = [998];
  observe railway::Segment::semaphores = [];
}

object o330 : railway::Segment {
  observe railway::RailwayElement::id = [314];
  observe railway::TrackElement::monitoredBy = [@o305];
  observe railway::TrackElement::connectsTo = [@o331];
  observe railway::Segment::length = [638];
  observe railway::Segment::semaphores = [];
}

object o331 : railway::Segment {
  observe railway::RailwayElement::id = [315];
  observe railway::TrackElement::monitoredBy = [@o305];
  observe railway::TrackElement::connectsTo = [@o332];
  observe railway::Segment::length = [669];
  observe railway::Segment::semaphores = [];
}

object o332 : railway::Segment {
  observe railway::RailwayElement::id = [316];
  observe railway::TrackElement::monitoredBy = [@o305];
  observe railway::TrackElement::connectsTo = [@o333];
  observe railway::Segment::length = [546];
  observe railway::Segment::semaphores = [];
}

object o333 : railway::Segment {
  observe railway::RailwayElement::id = [318];
  observe railway::TrackElement::monitoredBy = [@o306];
  observe railway::TrackElement::connectsTo = [@o334];
  observe railway::Segment::length = [587];
  observe railway::Segment::semaphores = [];
}

object o334 : railway::Segment {
  observe railway::RailwayElement::id = [319];
  observe railway::TrackElement::monitoredBy = [@o306];
  observe railway::TrackElement::connectsTo = [@o335];
  observe railway::Segment::length = [827];
  observe railway::Segment::semaphores = [];
}

object o335 : railway::Segment {
  observe railway::RailwayElement::id = [320];
  observe railway::TrackElement::monitoredBy = [@o306];
  observe railway::TrackElement::connectsTo = [@o336];
  observe railway::Segment::length = [941];
  observe railway::Segment::semaphores = [];
}

object o336 : railway::Segment {
  observe railway::RailwayElement::id = [321];
  observe railway::TrackElement::monitoredBy = [@o306];
  observe railway::TrackElement::connectsTo = [@o337];
  observe railway::Segment::length = [26];
  observe railway::Segment::semaphores = [];
}

object o337 : railway::Segment {
  observe railway::RailwayElement::id = [322];
  observe railway::TrackElement::monitoredBy = [@o306];
  observe railway::TrackElement::connectsTo = [@o338];
  observe railway::Segment::length = [939];
  observe railway::Segment::semaphores = [];
}

object o338 : railway::Segment {
  observe railway::RailwayElement::id = [324];
  observe railway::TrackElement::monitoredBy = [@o307];
  observe railway::TrackElement::connectsTo = [@o339];
  observe railway::Segment::length = [611];
  observe railway::Segment::semaphores = [];
}

object o339 : railway::Segment {
  observe railway::RailwayElement::id = [325];
  observe railway::TrackElement::monitoredBy = [@o307];
  observe railway::TrackElement::connectsTo = [@o340];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [];
}

object o340 : railway::Segment {
  observe railway::RailwayElement::id = [326];
  observe railway::TrackElement::monitoredBy = [@o307];
  observe railway::TrackElement::connectsTo = [@o341];
  observe railway::Segment::length = [994];
  observe railway::Segment::semaphores = [];
}

object o341 : railway::Segment {
  observe railway::RailwayElement::id = [327];
  observe railway::TrackElement::monitoredBy = [@o307];
  observe railway::TrackElement::connectsTo = [@o342];
  observe railway::Segment::length = [837];
  observe railway::Segment::semaphores = [];
}

object o342 : railway::Segment {
  observe railway::RailwayElement::id = [328];
  observe railway::TrackElement::monitoredBy = [@o307];
  observe railway::TrackElement::connectsTo = [@o343];
  observe railway::Segment::length = [479];
  observe railway::Segment::semaphores = [];
}

object o343 : railway::Segment {
  observe railway::RailwayElement::id = [330];
  observe railway::TrackElement::monitoredBy = [@o308];
  observe railway::TrackElement::connectsTo = [@o344];
  observe railway::Segment::length = [307];
  observe railway::Segment::semaphores = [];
}

object o344 : railway::Segment {
  observe railway::RailwayElement::id = [331];
  observe railway::TrackElement::monitoredBy = [@o308];
  observe railway::TrackElement::connectsTo = [@o345];
  observe railway::Segment::length = [283];
  observe railway::Segment::semaphores = [];
}

object o345 : railway::Segment {
  observe railway::RailwayElement::id = [332];
  observe railway::TrackElement::monitoredBy = [@o308];
  observe railway::TrackElement::connectsTo = [@o346];
  observe railway::Segment::length = [52];
  observe railway::Segment::semaphores = [];
}

object o346 : railway::Segment {
  observe railway::RailwayElement::id = [333];
  observe railway::TrackElement::monitoredBy = [@o308];
  observe railway::TrackElement::connectsTo = [@o347];
  observe railway::Segment::length = [694];
  observe railway::Segment::semaphores = [];
}

object o347 : railway::Segment {
  observe railway::RailwayElement::id = [334];
  observe railway::TrackElement::monitoredBy = [@o308];
  observe railway::TrackElement::connectsTo = [@o348];
  observe railway::Segment::length = [895];
  observe railway::Segment::semaphores = [];
}

object o348 : railway::Segment {
  observe railway::RailwayElement::id = [336];
  observe railway::TrackElement::monitoredBy = [@o309];
  observe railway::TrackElement::connectsTo = [@o349];
  observe railway::Segment::length = [62];
  observe railway::Segment::semaphores = [];
}

object o349 : railway::Segment {
  observe railway::RailwayElement::id = [337];
  observe railway::TrackElement::monitoredBy = [@o309];
  observe railway::TrackElement::connectsTo = [@o350];
  observe railway::Segment::length = [57];
  observe railway::Segment::semaphores = [];
}

object o350 : railway::Segment {
  observe railway::RailwayElement::id = [338];
  observe railway::TrackElement::monitoredBy = [@o309];
  observe railway::TrackElement::connectsTo = [@o351];
  observe railway::Segment::length = [250];
  observe railway::Segment::semaphores = [];
}

object o351 : railway::Segment {
  observe railway::RailwayElement::id = [339];
  observe railway::TrackElement::monitoredBy = [@o309];
  observe railway::TrackElement::connectsTo = [@o352];
  observe railway::Segment::length = [935];
  observe railway::Segment::semaphores = [];
}

object o352 : railway::Segment {
  observe railway::RailwayElement::id = [340];
  observe railway::TrackElement::monitoredBy = [@o309];
  observe railway::TrackElement::connectsTo = [@o353];
  observe railway::Segment::length = [235];
  observe railway::Segment::semaphores = [];
}

object o353 : railway::Segment {
  observe railway::RailwayElement::id = [342];
  observe railway::TrackElement::monitoredBy = [@o310];
  observe railway::TrackElement::connectsTo = [@o354];
  observe railway::Segment::length = [795];
  observe railway::Segment::semaphores = [];
}

object o354 : railway::Segment {
  observe railway::RailwayElement::id = [343];
  observe railway::TrackElement::monitoredBy = [@o310];
  observe railway::TrackElement::connectsTo = [@o355];
  observe railway::Segment::length = [392];
  observe railway::Segment::semaphores = [];
}

object o355 : railway::Segment {
  observe railway::RailwayElement::id = [344];
  observe railway::TrackElement::monitoredBy = [@o310];
  observe railway::TrackElement::connectsTo = [@o356];
  observe railway::Segment::length = [628];
  observe railway::Segment::semaphores = [];
}

object o356 : railway::Segment {
  observe railway::RailwayElement::id = [345];
  observe railway::TrackElement::monitoredBy = [@o310];
  observe railway::TrackElement::connectsTo = [@o357];
  observe railway::Segment::length = [558];
  observe railway::Segment::semaphores = [];
}

object o357 : railway::Segment {
  observe railway::RailwayElement::id = [346];
  observe railway::TrackElement::monitoredBy = [@o310];
  observe railway::TrackElement::connectsTo = [@o423];
  observe railway::Segment::length = [110];
  observe railway::Segment::semaphores = [];
}

object o358 : railway::Region {
  observe railway::RailwayElement::id = [349];
  observe railway::Region::sensors = [@o359, @o360, @o361, @o362, @o363, @o364, @o365, @o366, @o367, @o368, @o369, @o370, @o371, @o372, @o373, @o374, @o375, @o376, @o377, @o378, @o379, @o380, @o381, @o382, @o383, @o384, @o385, @o386, @o387, @o388, @o389, @o390, @o391, @o392, @o393, @o394, @o395, @o396, @o397, @o398, @o399, @o400, @o401, @o402, @o403, @o404, @o405, @o406, @o407, @o408, @o409, @o410, @o411, @o412, @o413, @o414, @o415, @o416, @o417, @o418, @o419, @o420, @o421, @o422];
  observe railway::Region::elements = [@o423, @o424, @o426, @o427, @o428, @o429, @o430, @o431, @o432, @o433, @o434, @o435, @o436, @o437, @o438, @o439, @o440, @o441, @o442, @o443, @o444, @o445, @o446, @o447, @o448, @o449, @o450, @o451, @o452, @o453, @o454, @o455, @o456, @o457, @o458, @o459, @o460, @o461, @o462, @o463, @o464, @o465, @o466, @o467, @o468, @o469, @o470, @o471, @o472, @o473, @o474, @o475, @o476, @o477, @o478, @o479, @o480, @o481, @o482, @o483, @o484, @o485, @o486, @o487, @o488, @o489, @o490, @o491, @o492, @o493, @o494, @o495, @o496, @o497, @o498, @o499, @o500, @o501, @o502, @o503, @o504, @o505, @o506, @o507, @o508, @o509, @o510, @o511, @o512, @o513, @o514, @o515, @o516, @o517, @o518, @o519, @o520, @o521, @o522, @o523, @o524, @o525, @o526, @o527, @o528, @o529, @o530, @o531, @o532, @o533, @o534, @o535, @o536, @o537, @o538, @o539, @o540, @o541, @o542, @o543, @o544, @o545, @o546, @o547, @o548, @o549, @o550, @o551, @o552, @o553, @o554, @o555, @o556, @o557, @o558, @o559, @o560, @o561, @o562, @o563, @o564, @o565, @o566, @o567, @o568, @o569, @o570, @o571, @o572, @o573, @o574, @o575, @o576, @o577, @o578, @o579, @o580, @o581, @o582, @o583, @o584, @o585, @o586, @o587, @o588, @o589, @o590, @o591, @o592, @o593, @o594, @o595, @o596, @o597, @o598, @o599, @o600, @o601, @o602, @o603, @o604, @o605, @o606, @o607, @o608, @o609, @o610, @o611, @o612, @o613, @o614, @o615, @o616, @o617, @o618, @o619, @o620, @o621, @o622, @o623, @o624, @o625, @o626, @o627, @o628, @o629, @o630, @o631, @o632, @o633, @o634, @o635, @o636, @o637, @o638, @o639, @o640, @o641, @o642, @o643, @o644, @o645, @o646, @o647, @o648, @o649, @o650, @o651, @o652, @o653, @o654, @o655, @o656, @o657, @o658, @o659, @o660, @o661, @o662, @o663, @o664, @o665, @o666, @o667, @o668, @o669, @o670, @o671, @o672, @o673, @o674, @o675, @o676, @o677, @o678, @o679, @o680, @o681, @o682, @o683, @o684, @o685, @o686, @o687, @o688, @o689, @o690, @o691, @o692, @o693, @o694, @o695, @o696, @o697, @o698, @o699, @o700, @o701, @o702, @o703, @o704, @o705, @o706, @o707, @o708, @o709, @o710, @o711, @o712, @o713, @o714, @o715, @o716, @o717, @o718, @o719, @o720, @o721, @o722, @o723, @o724, @o725, @o726, @o727, @o728, @o729, @o730, @o731, @o732, @o733, @o734, @o735, @o736, @o737, @o738, @o739, @o740, @o741, @o742, @o743, @o744, @o745, @o746, @o747, @o748, @o749, @o750, @o751, @o752, @o753];
}

object o359 : railway::Sensor {
  observe railway::RailwayElement::id = [351];
  observe railway::Sensor::monitors = [@o423, @o424, @o426, @o427, @o428, @o429];
}

object o360 : railway::Sensor {
  observe railway::RailwayElement::id = [357];
  observe railway::Sensor::monitors = [@o423, @o430, @o431, @o432, @o433, @o434];
}

object o361 : railway::Sensor {
  observe railway::RailwayElement::id = [363];
  observe railway::Sensor::monitors = [@o423, @o435, @o436, @o437, @o438, @o439];
}

object o362 : railway::Sensor {
  observe railway::RailwayElement::id = [369];
  observe railway::Sensor::monitors = [@o423, @o440, @o441, @o442, @o443, @o444];
}

object o363 : railway::Sensor {
  observe railway::RailwayElement::id = [375];
  observe railway::Sensor::monitors = [@o423, @o445, @o446, @o447, @o448, @o449];
}

object o364 : railway::Sensor {
  observe railway::RailwayElement::id = [381];
  observe railway::Sensor::monitors = [@o423, @o450, @o451, @o452, @o453, @o454];
}

object o365 : railway::Sensor {
  observe railway::RailwayElement::id = [387];
  observe railway::Sensor::monitors = [@o423, @o455, @o456, @o457, @o458, @o459];
}

object o366 : railway::Sensor {
  observe railway::RailwayElement::id = [393];
  observe railway::Sensor::monitors = [@o423, @o460, @o461, @o462, @o463, @o464];
}

object o367 : railway::Sensor {
  observe railway::RailwayElement::id = [399];
  observe railway::Sensor::monitors = [@o423, @o465, @o466, @o467, @o468, @o469];
}

object o368 : railway::Sensor {
  observe railway::RailwayElement::id = [407];
  observe railway::Sensor::monitors = [@o470, @o471, @o472, @o473, @o474, @o475];
}

object o369 : railway::Sensor {
  observe railway::RailwayElement::id = [413];
  observe railway::Sensor::monitors = [@o470, @o476, @o477, @o478, @o479, @o480];
}

object o370 : railway::Sensor {
  observe railway::RailwayElement::id = [419];
  observe railway::Sensor::monitors = [@o470, @o481, @o482, @o483, @o484, @o485];
}

object o371 : railway::Sensor {
  observe railway::RailwayElement::id = [425];
  observe railway::Sensor::monitors = [@o470, @o486, @o487, @o488, @o489, @o490];
}

object o372 : railway::Sensor {
  observe railway::RailwayElement::id = [431];
  observe railway::Sensor::monitors = [@o470, @o491, @o492, @o493, @o494, @o495];
}

object o373 : railway::Sensor {
  observe railway::RailwayElement::id = [437];
  observe railway::Sensor::monitors = [@o470, @o496, @o497, @o498, @o499, @o500];
}

object o374 : railway::Sensor {
  observe railway::RailwayElement::id = [443];
  observe railway::Sensor::monitors = [@o470, @o501, @o502, @o503, @o504, @o505];
}

object o375 : railway::Sensor {
  observe railway::RailwayElement::id = [449];
  observe railway::Sensor::monitors = [@o470, @o506, @o507, @o508, @o509, @o510];
}

object o376 : railway::Sensor {
  observe railway::RailwayElement::id = [455];
  observe railway::Sensor::monitors = [@o470, @o511, @o512, @o513, @o514, @o515];
}

object o377 : railway::Sensor {
  observe railway::RailwayElement::id = [463];
  observe railway::Sensor::monitors = [@o516, @o517, @o518, @o519, @o520, @o521];
}

object o378 : railway::Sensor {
  observe railway::RailwayElement::id = [471];
  observe railway::Sensor::monitors = [@o522, @o523, @o524, @o525, @o526, @o527];
}

object o379 : railway::Sensor {
  observe railway::RailwayElement::id = [477];
  observe railway::Sensor::monitors = [@o522, @o528, @o529, @o530, @o531, @o532];
}

object o380 : railway::Sensor {
  observe railway::RailwayElement::id = [483];
  observe railway::Sensor::monitors = [@o522, @o533, @o534, @o535, @o536, @o537];
}

object o381 : railway::Sensor {
  observe railway::RailwayElement::id = [489];
  observe railway::Sensor::monitors = [@o522, @o538, @o539, @o540, @o541, @o542];
}

object o382 : railway::Sensor {
  observe railway::RailwayElement::id = [495];
  observe railway::Sensor::monitors = [@o522, @o543, @o544, @o545, @o546, @o547];
}

object o383 : railway::Sensor {
  observe railway::RailwayElement::id = [501];
  observe railway::Sensor::monitors = [@o522, @o548, @o549, @o550, @o551, @o552];
}

object o384 : railway::Sensor {
  observe railway::RailwayElement::id = [507];
  observe railway::Sensor::monitors = [@o522, @o553, @o554, @o555, @o556, @o557];
}

object o385 : railway::Sensor {
  observe railway::RailwayElement::id = [513];
  observe railway::Sensor::monitors = [@o522, @o558, @o559, @o560, @o561, @o562];
}

object o386 : railway::Sensor {
  observe railway::RailwayElement::id = [519];
  observe railway::Sensor::monitors = [@o522, @o563, @o564, @o565, @o566, @o567];
}

object o387 : railway::Sensor {
  observe railway::RailwayElement::id = [527];
  observe railway::Sensor::monitors = [@o568, @o569, @o570, @o571, @o572, @o573];
}

object o388 : railway::Sensor {
  observe railway::RailwayElement::id = [533];
  observe railway::Sensor::monitors = [@o568, @o574, @o575, @o576, @o577, @o578];
}

object o389 : railway::Sensor {
  observe railway::RailwayElement::id = [539];
  observe railway::Sensor::monitors = [@o568, @o579, @o580, @o581, @o582, @o583];
}

object o390 : railway::Sensor {
  observe railway::RailwayElement::id = [545];
  observe railway::Sensor::monitors = [@o568, @o584, @o585, @o586, @o587, @o588];
}

object o391 : railway::Sensor {
  observe railway::RailwayElement::id = [551];
  observe railway::Sensor::monitors = [@o568, @o589, @o590, @o591, @o592, @o593];
}

object o392 : railway::Sensor {
  observe railway::RailwayElement::id = [557];
  observe railway::Sensor::monitors = [@o568, @o594, @o595, @o596, @o597, @o598];
}

object o393 : railway::Sensor {
  observe railway::RailwayElement::id = [563];
  observe railway::Sensor::monitors = [@o568, @o599, @o600, @o601, @o602, @o603];
}

object o394 : railway::Sensor {
  observe railway::RailwayElement::id = [569];
  observe railway::Sensor::monitors = [@o568, @o604, @o605, @o606, @o607, @o608];
}

object o395 : railway::Sensor {
  observe railway::RailwayElement::id = [575];
  observe railway::Sensor::monitors = [@o568, @o609, @o610, @o611, @o612, @o613];
}

object o396 : railway::Sensor {
  observe railway::RailwayElement::id = [583];
  observe railway::Sensor::monitors = [@o614, @o615, @o616, @o617, @o618, @o619];
}

object o397 : railway::Sensor {
  observe railway::RailwayElement::id = [589];
  observe railway::Sensor::monitors = [@o614, @o620, @o621, @o622, @o623, @o624];
}

object o398 : railway::Sensor {
  observe railway::RailwayElement::id = [595];
  observe railway::Sensor::monitors = [@o614, @o625, @o626, @o627, @o628, @o629];
}

object o399 : railway::Sensor {
  observe railway::RailwayElement::id = [601];
  observe railway::Sensor::monitors = [@o614, @o630, @o631, @o632, @o633, @o634];
}

object o400 : railway::Sensor {
  observe railway::RailwayElement::id = [607];
  observe railway::Sensor::monitors = [@o614, @o635, @o636, @o637, @o638, @o639];
}

object o401 : railway::Sensor {
  observe railway::RailwayElement::id = [615];
  observe railway::Sensor::monitors = [@o640, @o641, @o642, @o643, @o644, @o645];
}

object o402 : railway::Sensor {
  observe railway::RailwayElement::id = [623];
  observe railway::Sensor::monitors = [@o646, @o647, @o648, @o649, @o650, @o651];
}

object o403 : railway::Sensor {
  observe railway::RailwayElement::id = [629];
  observe railway::Sensor::monitors = [@o646, @o652, @o653, @o654, @o655, @o656];
}

object o404 : railway::Sensor {
  observe railway::RailwayElement::id = [635];
  observe railway::Sensor::monitors = [@o646, @o657, @o658, @o659, @o660, @o661];
}

object o405 : railway::Sensor {
  observe railway::RailwayElement::id = [641];
  observe railway::Sensor::monitors = [@o646, @o662, @o663, @o664, @o665, @o666];
}

object o406 : railway::Sensor {
  observe railway::RailwayElement::id = [647];
  observe railway::Sensor::monitors = [@o646, @o667, @o668, @o669, @o670, @o671];
}

object o407 : railway::Sensor {
  observe railway::RailwayElement::id = [653];
  observe railway::Sensor::monitors = [@o646, @o672, @o673, @o674, @o675, @o676];
}

object o408 : railway::Sensor {
  observe railway::RailwayElement::id = [659];
  observe railway::Sensor::monitors = [@o646, @o677, @o678, @o679, @o680, @o681];
}

object o409 : railway::Sensor {
  observe railway::RailwayElement::id = [665];
  observe railway::Sensor::monitors = [@o646, @o682, @o683, @o684, @o685, @o686];
}

object o410 : railway::Sensor {
  observe railway::RailwayElement::id = [671];
  observe railway::Sensor::monitors = [@o646, @o687, @o688, @o689, @o690, @o691];
}

object o411 : railway::Sensor {
  observe railway::RailwayElement::id = [679];
  observe railway::Sensor::monitors = [@o692, @o693, @o694, @o695, @o696, @o697];
}

object o412 : railway::Sensor {
  observe railway::RailwayElement::id = [685];
  observe railway::Sensor::monitors = [@o692, @o698, @o699, @o700, @o701, @o702];
}

object o413 : railway::Sensor {
  observe railway::RailwayElement::id = [691];
  observe railway::Sensor::monitors = [@o692, @o703, @o704, @o705, @o706, @o707];
}

object o414 : railway::Sensor {
  observe railway::RailwayElement::id = [697];
  observe railway::Sensor::monitors = [@o692, @o708, @o709, @o710, @o711, @o712];
}

object o415 : railway::Sensor {
  observe railway::RailwayElement::id = [703];
  observe railway::Sensor::monitors = [@o692, @o713, @o714, @o715, @o716, @o717];
}

object o416 : railway::Sensor {
  observe railway::RailwayElement::id = [709];
  observe railway::Sensor::monitors = [@o692, @o718, @o719, @o720, @o721, @o722];
}

object o417 : railway::Sensor {
  observe railway::RailwayElement::id = [715];
  observe railway::Sensor::monitors = [@o692, @o723, @o724, @o725, @o726, @o727];
}

object o418 : railway::Sensor {
  observe railway::RailwayElement::id = [723];
  observe railway::Sensor::monitors = [@o728, @o729, @o730, @o731, @o732, @o733];
}

object o419 : railway::Sensor {
  observe railway::RailwayElement::id = [729];
  observe railway::Sensor::monitors = [@o728, @o734, @o735, @o736, @o737, @o738];
}

object o420 : railway::Sensor {
  observe railway::RailwayElement::id = [735];
  observe railway::Sensor::monitors = [@o728, @o739, @o740, @o741, @o742, @o743];
}

object o421 : railway::Sensor {
  observe railway::RailwayElement::id = [741];
  observe railway::Sensor::monitors = [@o728, @o744, @o745, @o746, @o747, @o748];
}

object o422 : railway::Sensor {
  observe railway::RailwayElement::id = [747];
  observe railway::Sensor::monitors = [@o728, @o749, @o750, @o751, @o752, @o753];
}

object o423 : railway::Switch {
  observe railway::RailwayElement::id = [350];
  observe railway::TrackElement::monitoredBy = [@o359, @o360, @o361, @o362, @o363, @o364, @o365, @o366, @o367];
  observe railway::TrackElement::connectsTo = [@o424];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o14];
}

object o424 : railway::Segment {
  observe railway::RailwayElement::id = [352];
  observe railway::TrackElement::monitoredBy = [@o359];
  observe railway::TrackElement::connectsTo = [@o426];
  observe railway::Segment::length = [557];
  observe railway::Segment::semaphores = [@o425];
}

object o425 : railway::Semaphore {
  observe railway::RailwayElement::id = [1];
  observe railway::Semaphore::signal = [railway::Signal::GO];
}

object o426 : railway::Segment {
  observe railway::RailwayElement::id = [353];
  observe railway::TrackElement::monitoredBy = [@o359];
  observe railway::TrackElement::connectsTo = [@o427];
  observe railway::Segment::length = [132];
  observe railway::Segment::semaphores = [];
}

object o427 : railway::Segment {
  observe railway::RailwayElement::id = [354];
  observe railway::TrackElement::monitoredBy = [@o359];
  observe railway::TrackElement::connectsTo = [@o428];
  observe railway::Segment::length = [455];
  observe railway::Segment::semaphores = [];
}

object o428 : railway::Segment {
  observe railway::RailwayElement::id = [355];
  observe railway::TrackElement::monitoredBy = [@o359];
  observe railway::TrackElement::connectsTo = [@o429];
  observe railway::Segment::length = [678];
  observe railway::Segment::semaphores = [];
}

object o429 : railway::Segment {
  observe railway::RailwayElement::id = [356];
  observe railway::TrackElement::monitoredBy = [@o359];
  observe railway::TrackElement::connectsTo = [@o430];
  observe railway::Segment::length = [489];
  observe railway::Segment::semaphores = [];
}

object o430 : railway::Segment {
  observe railway::RailwayElement::id = [358];
  observe railway::TrackElement::monitoredBy = [@o360];
  observe railway::TrackElement::connectsTo = [@o431];
  observe railway::Segment::length = [5];
  observe railway::Segment::semaphores = [];
}

object o431 : railway::Segment {
  observe railway::RailwayElement::id = [359];
  observe railway::TrackElement::monitoredBy = [@o360];
  observe railway::TrackElement::connectsTo = [@o432];
  observe railway::Segment::length = [682];
  observe railway::Segment::semaphores = [];
}

object o432 : railway::Segment {
  observe railway::RailwayElement::id = [360];
  observe railway::TrackElement::monitoredBy = [@o360];
  observe railway::TrackElement::connectsTo = [@o433];
  observe railway::Segment::length = [76];
  observe railway::Segment::semaphores = [];
}

object o433 : railway::Segment {
  observe railway::RailwayElement::id = [361];
  observe railway::TrackElement::monitoredBy = [@o360];
  observe railway::TrackElement::connectsTo = [@o434];
  observe railway::Segment::length = [169];
  observe railway::Segment::semaphores = [];
}

object o434 : railway::Segment {
  observe railway::RailwayElement::id = [362];
  observe railway::TrackElement::monitoredBy = [@o360];
  observe railway::TrackElement::connectsTo = [@o435];
  observe railway::Segment::length = [171];
  observe railway::Segment::semaphores = [];
}

object o435 : railway::Segment {
  observe railway::RailwayElement::id = [364];
  observe railway::TrackElement::monitoredBy = [@o361];
  observe railway::TrackElement::connectsTo = [@o436];
  observe railway::Segment::length = [726];
  observe railway::Segment::semaphores = [];
}

object o436 : railway::Segment {
  observe railway::RailwayElement::id = [365];
  observe railway::TrackElement::monitoredBy = [@o361];
  observe railway::TrackElement::connectsTo = [@o437];
  observe railway::Segment::length = [421];
  observe railway::Segment::semaphores = [];
}

object o437 : railway::Segment {
  observe railway::RailwayElement::id = [366];
  observe railway::TrackElement::monitoredBy = [@o361];
  observe railway::TrackElement::connectsTo = [@o438];
  observe railway::Segment::length = [188];
  observe railway::Segment::semaphores = [];
}

object o438 : railway::Segment {
  observe railway::RailwayElement::id = [367];
  observe railway::TrackElement::monitoredBy = [@o361];
  observe railway::TrackElement::connectsTo = [@o439];
  observe railway::Segment::length = [149];
  observe railway::Segment::semaphores = [];
}

object o439 : railway::Segment {
  observe railway::RailwayElement::id = [368];
  observe railway::TrackElement::monitoredBy = [@o361];
  observe railway::TrackElement::connectsTo = [@o440];
  observe railway::Segment::length = [413];
  observe railway::Segment::semaphores = [];
}

object o440 : railway::Segment {
  observe railway::RailwayElement::id = [370];
  observe railway::TrackElement::monitoredBy = [@o362];
  observe railway::TrackElement::connectsTo = [@o441];
  observe railway::Segment::length = [531];
  observe railway::Segment::semaphores = [];
}

object o441 : railway::Segment {
  observe railway::RailwayElement::id = [371];
  observe railway::TrackElement::monitoredBy = [@o362];
  observe railway::TrackElement::connectsTo = [@o442];
  observe railway::Segment::length = [36];
  observe railway::Segment::semaphores = [];
}

object o442 : railway::Segment {
  observe railway::RailwayElement::id = [372];
  observe railway::TrackElement::monitoredBy = [@o362];
  observe railway::TrackElement::connectsTo = [@o443];
  observe railway::Segment::length = [578];
  observe railway::Segment::semaphores = [];
}

object o443 : railway::Segment {
  observe railway::RailwayElement::id = [373];
  observe railway::TrackElement::monitoredBy = [@o362];
  observe railway::TrackElement::connectsTo = [@o444];
  observe railway::Segment::length = [322];
  observe railway::Segment::semaphores = [];
}

object o444 : railway::Segment {
  observe railway::RailwayElement::id = [374];
  observe railway::TrackElement::monitoredBy = [@o362];
  observe railway::TrackElement::connectsTo = [@o445];
  observe railway::Segment::length = [563];
  observe railway::Segment::semaphores = [];
}

object o445 : railway::Segment {
  observe railway::RailwayElement::id = [376];
  observe railway::TrackElement::monitoredBy = [@o363];
  observe railway::TrackElement::connectsTo = [@o446];
  observe railway::Segment::length = [252];
  observe railway::Segment::semaphores = [];
}

object o446 : railway::Segment {
  observe railway::RailwayElement::id = [377];
  observe railway::TrackElement::monitoredBy = [@o363];
  observe railway::TrackElement::connectsTo = [@o447];
  observe railway::Segment::length = [611];
  observe railway::Segment::semaphores = [];
}

object o447 : railway::Segment {
  observe railway::RailwayElement::id = [378];
  observe railway::TrackElement::monitoredBy = [@o363];
  observe railway::TrackElement::connectsTo = [@o448];
  observe railway::Segment::length = [98];
  observe railway::Segment::semaphores = [];
}

object o448 : railway::Segment {
  observe railway::RailwayElement::id = [379];
  observe railway::TrackElement::monitoredBy = [@o363];
  observe railway::TrackElement::connectsTo = [@o449];
  observe railway::Segment::length = [107];
  observe railway::Segment::semaphores = [];
}

object o449 : railway::Segment {
  observe railway::RailwayElement::id = [380];
  observe railway::TrackElement::monitoredBy = [@o363];
  observe railway::TrackElement::connectsTo = [@o450];
  observe railway::Segment::length = [360];
  observe railway::Segment::semaphores = [];
}

object o450 : railway::Segment {
  observe railway::RailwayElement::id = [382];
  observe railway::TrackElement::monitoredBy = [@o364];
  observe railway::TrackElement::connectsTo = [@o451];
  observe railway::Segment::length = [387];
  observe railway::Segment::semaphores = [];
}

object o451 : railway::Segment {
  observe railway::RailwayElement::id = [383];
  observe railway::TrackElement::monitoredBy = [@o364];
  observe railway::TrackElement::connectsTo = [@o452];
  observe railway::Segment::length = [12];
  observe railway::Segment::semaphores = [];
}

object o452 : railway::Segment {
  observe railway::RailwayElement::id = [384];
  observe railway::TrackElement::monitoredBy = [@o364];
  observe railway::TrackElement::connectsTo = [@o453];
  observe railway::Segment::length = [480];
  observe railway::Segment::semaphores = [];
}

object o453 : railway::Segment {
  observe railway::RailwayElement::id = [385];
  observe railway::TrackElement::monitoredBy = [@o364];
  observe railway::TrackElement::connectsTo = [@o454];
  observe railway::Segment::length = [148];
  observe railway::Segment::semaphores = [];
}

object o454 : railway::Segment {
  observe railway::RailwayElement::id = [386];
  observe railway::TrackElement::monitoredBy = [@o364];
  observe railway::TrackElement::connectsTo = [@o455];
  observe railway::Segment::length = [94];
  observe railway::Segment::semaphores = [];
}

object o455 : railway::Segment {
  observe railway::RailwayElement::id = [388];
  observe railway::TrackElement::monitoredBy = [@o365];
  observe railway::TrackElement::connectsTo = [@o456];
  observe railway::Segment::length = [686];
  observe railway::Segment::semaphores = [];
}

object o456 : railway::Segment {
  observe railway::RailwayElement::id = [389];
  observe railway::TrackElement::monitoredBy = [@o365];
  observe railway::TrackElement::connectsTo = [@o457];
  observe railway::Segment::length = [810];
  observe railway::Segment::semaphores = [];
}

object o457 : railway::Segment {
  observe railway::RailwayElement::id = [390];
  observe railway::TrackElement::monitoredBy = [@o365];
  observe railway::TrackElement::connectsTo = [@o458];
  observe railway::Segment::length = [659];
  observe railway::Segment::semaphores = [];
}

object o458 : railway::Segment {
  observe railway::RailwayElement::id = [391];
  observe railway::TrackElement::monitoredBy = [@o365];
  observe railway::TrackElement::connectsTo = [@o459];
  observe railway::Segment::length = [630];
  observe railway::Segment::semaphores = [];
}

object o459 : railway::Segment {
  observe railway::RailwayElement::id = [392];
  observe railway::TrackElement::monitoredBy = [@o365];
  observe railway::TrackElement::connectsTo = [@o460];
  observe railway::Segment::length = [6];
  observe railway::Segment::semaphores = [];
}

object o460 : railway::Segment {
  observe railway::RailwayElement::id = [394];
  observe railway::TrackElement::monitoredBy = [@o366];
  observe railway::TrackElement::connectsTo = [@o461];
  observe railway::Segment::length = [501];
  observe railway::Segment::semaphores = [];
}

object o461 : railway::Segment {
  observe railway::RailwayElement::id = [395];
  observe railway::TrackElement::monitoredBy = [@o366];
  observe railway::TrackElement::connectsTo = [@o462];
  observe railway::Segment::length = [555];
  observe railway::Segment::semaphores = [];
}

object o462 : railway::Segment {
  observe railway::RailwayElement::id = [396];
  observe railway::TrackElement::monitoredBy = [@o366];
  observe railway::TrackElement::connectsTo = [@o463];
  observe railway::Segment::length = [368];
  observe railway::Segment::semaphores = [];
}

object o463 : railway::Segment {
  observe railway::RailwayElement::id = [397];
  observe railway::TrackElement::monitoredBy = [@o366];
  observe railway::TrackElement::connectsTo = [@o464];
  observe railway::Segment::length = [777];
  observe railway::Segment::semaphores = [];
}

object o464 : railway::Segment {
  observe railway::RailwayElement::id = [398];
  observe railway::TrackElement::monitoredBy = [@o366];
  observe railway::TrackElement::connectsTo = [@o465];
  observe railway::Segment::length = [906];
  observe railway::Segment::semaphores = [];
}

object o465 : railway::Segment {
  observe railway::RailwayElement::id = [400];
  observe railway::TrackElement::monitoredBy = [@o367];
  observe railway::TrackElement::connectsTo = [@o466];
  observe railway::Segment::length = [585];
  observe railway::Segment::semaphores = [];
}

object o466 : railway::Segment {
  observe railway::RailwayElement::id = [401];
  observe railway::TrackElement::monitoredBy = [@o367];
  observe railway::TrackElement::connectsTo = [@o467];
  observe railway::Segment::length = [11];
  observe railway::Segment::semaphores = [];
}

object o467 : railway::Segment {
  observe railway::RailwayElement::id = [402];
  observe railway::TrackElement::monitoredBy = [@o367];
  observe railway::TrackElement::connectsTo = [@o468];
  observe railway::Segment::length = [287];
  observe railway::Segment::semaphores = [];
}

object o468 : railway::Segment {
  observe railway::RailwayElement::id = [403];
  observe railway::TrackElement::monitoredBy = [@o367];
  observe railway::TrackElement::connectsTo = [@o469];
  observe railway::Segment::length = [947];
  observe railway::Segment::semaphores = [];
}

object o469 : railway::Segment {
  observe railway::RailwayElement::id = [404];
  observe railway::TrackElement::monitoredBy = [@o367];
  observe railway::TrackElement::connectsTo = [@o470];
  observe railway::Segment::length = [106];
  observe railway::Segment::semaphores = [];
}

object o470 : railway::Switch {
  observe railway::RailwayElement::id = [406];
  observe railway::TrackElement::monitoredBy = [@o368, @o369, @o370, @o371, @o372, @o373, @o374, @o375, @o376];
  observe railway::TrackElement::connectsTo = [@o471];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@o15];
}

object o471 : railway::Segment {
  observe railway::RailwayElement::id = [408];
  observe railway::TrackElement::monitoredBy = [@o368];
  observe railway::TrackElement::connectsTo = [@o472];
  observe railway::Segment::length = [301];
  observe railway::Segment::semaphores = [];
}

object o472 : railway::Segment {
  observe railway::RailwayElement::id = [409];
  observe railway::TrackElement::monitoredBy = [@o368];
  observe railway::TrackElement::connectsTo = [@o473];
  observe railway::Segment::length = [836];
  observe railway::Segment::semaphores = [];
}

object o473 : railway::Segment {
  observe railway::RailwayElement::id = [410];
  observe railway::TrackElement::monitoredBy = [@o368];
  observe railway::TrackElement::connectsTo = [@o474];
  observe railway::Segment::length = [254];
  observe railway::Segment::semaphores = [];
}

object o474 : railway::Segment {
  observe railway::RailwayElement::id = [411];
  observe railway::TrackElement::monitoredBy = [@o368];
  observe railway::TrackElement::connectsTo = [@o475];
  observe railway::Segment::length = [422];
  observe railway::Segment::semaphores = [];
}

object o475 : railway::Segment {
  observe railway::RailwayElement::id = [412];
  observe railway::TrackElement::monitoredBy = [@o368];
  observe railway::TrackElement::connectsTo = [@o476];
  observe railway::Segment::length = [146];
  observe railway::Segment::semaphores = [];
}

object o476 : railway::Segment {
  observe railway::RailwayElement::id = [414];
  observe railway::TrackElement::monitoredBy = [@o369];
  observe railway::TrackElement::connectsTo = [@o477];
  observe railway::Segment::length = [710];
  observe railway::Segment::semaphores = [];
}

object o477 : railway::Segment {
  observe railway::RailwayElement::id = [415];
  observe railway::TrackElement::monitoredBy = [@o369];
  observe railway::TrackElement::connectsTo = [@o478];
  observe railway::Segment::length = [576];
  observe railway::Segment::semaphores = [];
}

object o478 : railway::Segment {
  observe railway::RailwayElement::id = [416];
  observe railway::TrackElement::monitoredBy = [@o369];
  observe railway::TrackElement::connectsTo = [@o479];
  observe railway::Segment::length = [481];
  observe railway::Segment::semaphores = [];
}

object o479 : railway::Segment {
  observe railway::RailwayElement::id = [417];
  observe railway::TrackElement::monitoredBy = [@o369];
  observe railway::TrackElement::connectsTo = [@o480];
  observe railway::Segment::length = [638];
  observe railway::Segment::semaphores = [];
}

object o480 : railway::Segment {
  observe railway::RailwayElement::id = [418];
  observe railway::TrackElement::monitoredBy = [@o369];
  observe railway::TrackElement::connectsTo = [@o481];
  observe railway::Segment::length = [781];
  observe railway::Segment::semaphores = [];
}

object o481 : railway::Segment {
  observe railway::RailwayElement::id = [420];
  observe railway::TrackElement::monitoredBy = [@o370];
  observe railway::TrackElement::connectsTo = [@o482];
  observe railway::Segment::length = [409];
  observe railway::Segment::semaphores = [];
}

object o482 : railway::Segment {
  observe railway::RailwayElement::id = [421];
  observe railway::TrackElement::monitoredBy = [@o370];
  observe railway::TrackElement::connectsTo = [@o483];
  observe railway::Segment::length = [78];
  observe railway::Segment::semaphores = [];
}

object o483 : railway::Segment {
  observe railway::RailwayElement::id = [422];
  observe railway::TrackElement::monitoredBy = [@o370];
  observe railway::TrackElement::connectsTo = [@o484];
  observe railway::Segment::length = [34];
  observe railway::Segment::semaphores = [];
}

object o484 : railway::Segment {
  observe railway::RailwayElement::id = [423];
  observe railway::TrackElement::monitoredBy = [@o370];
  observe railway::TrackElement::connectsTo = [@o485];
  observe railway::Segment::length = [510];
  observe railway::Segment::semaphores = [];
}

object o485 : railway::Segment {
  observe railway::RailwayElement::id = [424];
  observe railway::TrackElement::monitoredBy = [@o370];
  observe railway::TrackElement::connectsTo = [@o486];
  observe railway::Segment::length = [536];
  observe railway::Segment::semaphores = [];
}

object o486 : railway::Segment {
  observe railway::RailwayElement::id = [426];
  observe railway::TrackElement::monitoredBy = [@o371];
  observe railway::TrackElement::connectsTo = [@o487];
  observe railway::Segment::length = [851];
  observe railway::Segment::semaphores = [];
}

object o487 : railway::Segment {
  observe railway::RailwayElement::id = [427];
  observe railway::TrackElement::monitoredBy = [@o371];
  observe railway::TrackElement::connectsTo = [@o488];
  observe railway::Segment::length = [898];
  observe railway::Segment::semaphores = [];
}

object o488 : railway::Segment {
  observe railway::RailwayElement::id = [428];
  observe railway::TrackElement::monitoredBy = [@o371];
  observe railway::TrackElement::connectsTo = [@o489];
  observe railway::Segment::length = [731];
  observe railway::Segment::semaphores = [];
}

object o489 : railway::Segment {
  observe railway::RailwayElement::id = [429];
  observe railway::TrackElement::monitoredBy = [@o371];
  observe railway::TrackElement::connectsTo = [@o490];
  observe railway::Segment::length = [83];
  observe railway::Segment::semaphores = [];
}

object o490 : railway::Segment {
  observe railway::RailwayElement::id = [430];
  observe railway::TrackElement::monitoredBy = [@o371];
  observe railway::TrackElement::connectsTo = [@o491];
  observe railway::Segment::length = [796];
  observe railway::Segment::semaphores = [];
}

object o491 : railway::Segment {
  observe railway::RailwayElement::id = [432];
  observe railway::TrackElement::monitoredBy = [@o372];
  observe railway::TrackElement::connectsTo = [@o492];
  observe railway::Segment::length = [113];
  observe railway::Segment::semaphores = [];
}

object o492 : railway::Segment {
  observe railway::RailwayElement::id = [433];
  observe railway::TrackElement::monitoredBy = [@o372];
  observe railway::TrackElement::connectsTo = [@o493];
  observe railway::Segment::length = [3];
  observe railway::Segment::semaphores = [];
}

object o493 : railway::Segment {
  observe railway::RailwayElement::id = [434];
  observe railway::TrackElement::monitoredBy = [@o372];
  observe railway::TrackElement::connectsTo = [@o494];
  observe railway::Segment::length = [326];
  observe railway::Segment::semaphores = [];
}

object o494 : railway::Segment {
  observe railway::RailwayElement::id = [435];
  observe railway::TrackElement::monitoredBy = [@o372];
  observe railway::TrackElement::connectsTo = [@o495];
  observe railway::Segment::length = [100];
  observe railway::Segment::semaphores = [];
}

object o495 : railway::Segment {
  observe railway::RailwayElement::id = [436];
  observe railway::TrackElement::monitoredBy = [@o372];
  observe railway::TrackElement::connectsTo = [@o496];
  observe railway::Segment::length = [555];
  observe railway::Segment::semaphores = [];
}

object o496 : railway::Segment {
  observe railway::RailwayElement::id = [438];
  observe railway::TrackElement::monitoredBy = [@o373];
  observe railway::TrackElement::connectsTo = [@o497];
  observe railway::Segment::length = [290];
  observe railway::Segment::semaphores = [];
}

object o497 : railway::Segment {
  observe railway::RailwayElement::id = [439];
  observe railway::TrackElement::monitoredBy = [@o373];
  observe railway::TrackElement::connectsTo = [@o498];
  observe railway::Segment::length = [126];
  observe railway::Segment::semaphores = [];
}

object o498 : railway::Segment {
  observe railway::RailwayElement::id = [440];
  observe railway::TrackElement::monitoredBy = [@o373];
  observe railway::TrackElement::connectsTo = [@o499];
  observe railway::Segment::length = [620];
  observe railway::Segment::semaphores = [];
}

object o499 : railway::Segment {
  observe railway::RailwayElement::id = [441];
  observe railway::TrackElement::monitoredBy = [@o373];
  observe railway::TrackElement::connectsTo = [@o500];
  observe railway::Segment::length = [323];
  observe railway::Segment::semaphores = [];
}

object o500 : railway::Segment {
  observe railway::RailwayElement::id = [442];
  observe railway::TrackElement::monitoredBy = [@o373];
  observe railway::TrackElement::connectsTo = [@o501];
  observe railway::Segment::length = [333];
  observe railway::Segment::semaphores = [];
}

object o501 : railway::Segment {
  observe railway::RailwayElement::id = [444];
  observe railway::TrackElement::monitoredBy = [@o374];
  observe railway::TrackElement::connectsTo = [@o502];
  observe railway::Segment::length = [598];
  observe railway::Segment::semaphores = [];
}

object o502 : railway::Segment {
  observe railway::RailwayElement::id = [445];
  observe railway::TrackElement::monitoredBy = [@o374];
  observe railway::TrackElement::connectsTo = [@o503];
  observe railway::Segment::length = [172];
  observe railway::Segment::semaphores = [];
}

object o503 : railway::Segment {
  observe railway::RailwayElement::id = [446];
  observe railway::TrackElement::monitoredBy = [@o374];
  observe railway::TrackElement::connectsTo = [@o504];
  observe railway::Segment::length = [263];
  observe railway::Segment::semaphores = [];
}

object o504 : railway::Segment {
  observe railway::RailwayElement::id = [447];
  observe railway::TrackElement::monitoredBy = [@o374];
  observe railway::TrackElement::connectsTo = [@o505];
  observe railway::Segment::length = [411];
  observe railway::Segment::semaphores = [];
}

object o505 : railway::Segment {
  observe railway::RailwayElement::id = [448];
  observe railway::TrackElement::monitoredBy = [@o374];
  observe railway::TrackElement::connectsTo = [@o506];
  observe railway::Segment::length = [638];
  observe railway::Segment::semaphores = [];
}

object o506 : railway::Segment {
  observe railway::RailwayElement::id = [450];
  observe railway::TrackElement::monitoredBy = [@o375];
  observe railway::TrackElement::connectsTo = [@o507];
  observe railway::Segment::length = [421];
  observe railway::Segment::semaphores = [];
}

object o507 : railway::Segment {
  observe railway::RailwayElement::id = [451];
  observe railway::TrackElement::monitoredBy = [@o375];
  observe railway::TrackElement::connectsTo = [@o508];
  observe railway::Segment::length = [921];
  observe railway::Segment::semaphores = [];
}

object o508 : railway::Segment {
  observe railway::RailwayElement::id = [452];
  observe railway::TrackElement::monitoredBy = [@o375];
  observe railway::TrackElement::connectsTo = [@o509];
  observe railway::Segment::length = [40];
  observe railway::Segment::semaphores = [];
}

object o509 : railway::Segment {
  observe railway::RailwayElement::id = [453];
  observe railway::TrackElement::monitoredBy = [@o375];
  observe railway::TrackElement::connectsTo = [@o510];
  observe railway::Segment::length = [546];
  observe railway::Segment::semaphores = [];
}

object o510 : railway::Segment {
  observe railway::RailwayElement::id = [454];
  observe railway::TrackElement::monitoredBy = [@o375];
  observe railway::TrackElement::connectsTo = [@o511];
  observe railway::Segment::length = [208];
  observe railway::Segment::semaphores = [];
}

object o511 : railway::Segment {
  observe railway::RailwayElement::id = [456];
  observe railway::TrackElement::monitoredBy = [@o376];
  observe railway::TrackElement::connectsTo = [@o512];
  observe railway::Segment::length = [542];
  observe railway::Segment::semaphores = [];
}

object o512 : railway::Segment {
  observe railway::RailwayElement::id = [457];
  observe railway::TrackElement::monitoredBy = [@o376];
  observe railway::TrackElement::connectsTo = [@o513];
  observe railway::Segment::length = [770];
  observe railway::Segment::semaphores = [];
}

object o513 : railway::Segment {
  observe railway::RailwayElement::id = [458];
  observe railway::TrackElement::monitoredBy = [@o376];
  observe railway::TrackElement::connectsTo = [@o514];
  observe railway::Segment::length = [147];
  observe railway::Segment::semaphores = [];
}

object o514 : railway::Segment {
  observe railway::RailwayElement::id = [459];
  observe railway::TrackElement::monitoredBy = [@o376];
  observe railway::TrackElement::connectsTo = [@o515];
  observe railway::Segment::length = [170];
  observe railway::Segment::semaphores = [];
}

object o515 : railway::Segment {
  observe railway::RailwayElement::id = [460];
  observe railway::TrackElement::monitoredBy = [@o376];
  observe railway::TrackElement::connectsTo = [@o516];
  observe railway::Segment::length = [167];
  observe railway::Segment::semaphores = [];
}

object o516 : railway::Switch {
  observe railway::RailwayElement::id = [462];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o517];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o16];
}

object o517 : railway::Segment {
  observe railway::RailwayElement::id = [464];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o518];
  observe railway::Segment::length = [524];
  observe railway::Segment::semaphores = [];
}

object o518 : railway::Segment {
  observe railway::RailwayElement::id = [465];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o519];
  observe railway::Segment::length = [5];
  observe railway::Segment::semaphores = [];
}

object o519 : railway::Segment {
  observe railway::RailwayElement::id = [466];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o520];
  observe railway::Segment::length = [133];
  observe railway::Segment::semaphores = [];
}

object o520 : railway::Segment {
  observe railway::RailwayElement::id = [467];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o521];
  observe railway::Segment::length = [818];
  observe railway::Segment::semaphores = [];
}

object o521 : railway::Segment {
  observe railway::RailwayElement::id = [468];
  observe railway::TrackElement::monitoredBy = [@o377];
  observe railway::TrackElement::connectsTo = [@o522];
  observe railway::Segment::length = [980];
  observe railway::Segment::semaphores = [];
}

object o522 : railway::Switch {
  observe railway::RailwayElement::id = [470];
  observe railway::TrackElement::monitoredBy = [@o378, @o379, @o380, @o381, @o382, @o383, @o384, @o385, @o386];
  observe railway::TrackElement::connectsTo = [@o523];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o17];
}

object o523 : railway::Segment {
  observe railway::RailwayElement::id = [472];
  observe railway::TrackElement::monitoredBy = [@o378];
  observe railway::TrackElement::connectsTo = [@o524];
  observe railway::Segment::length = [152];
  observe railway::Segment::semaphores = [];
}

object o524 : railway::Segment {
  observe railway::RailwayElement::id = [473];
  observe railway::TrackElement::monitoredBy = [@o378];
  observe railway::TrackElement::connectsTo = [@o525];
  observe railway::Segment::length = [808];
  observe railway::Segment::semaphores = [];
}

object o525 : railway::Segment {
  observe railway::RailwayElement::id = [474];
  observe railway::TrackElement::monitoredBy = [@o378];
  observe railway::TrackElement::connectsTo = [@o526];
  observe railway::Segment::length = [94];
  observe railway::Segment::semaphores = [];
}

object o526 : railway::Segment {
  observe railway::RailwayElement::id = [475];
  observe railway::TrackElement::monitoredBy = [@o378];
  observe railway::TrackElement::connectsTo = [@o527];
  observe railway::Segment::length = [768];
  observe railway::Segment::semaphores = [];
}

object o527 : railway::Segment {
  observe railway::RailwayElement::id = [476];
  observe railway::TrackElement::monitoredBy = [@o378];
  observe railway::TrackElement::connectsTo = [@o528];
  observe railway::Segment::length = [969];
  observe railway::Segment::semaphores = [];
}

object o528 : railway::Segment {
  observe railway::RailwayElement::id = [478];
  observe railway::TrackElement::monitoredBy = [@o379];
  observe railway::TrackElement::connectsTo = [@o529];
  observe railway::Segment::length = [948];
  observe railway::Segment::semaphores = [];
}

object o529 : railway::Segment {
  observe railway::RailwayElement::id = [479];
  observe railway::TrackElement::monitoredBy = [@o379];
  observe railway::TrackElement::connectsTo = [@o530];
  observe railway::Segment::length = [366];
  observe railway::Segment::semaphores = [];
}

object o530 : railway::Segment {
  observe railway::RailwayElement::id = [480];
  observe railway::TrackElement::monitoredBy = [@o379];
  observe railway::TrackElement::connectsTo = [@o531];
  observe railway::Segment::length = [971];
  observe railway::Segment::semaphores = [];
}

object o531 : railway::Segment {
  observe railway::RailwayElement::id = [481];
  observe railway::TrackElement::monitoredBy = [@o379];
  observe railway::TrackElement::connectsTo = [@o532];
  observe railway::Segment::length = [75];
  observe railway::Segment::semaphores = [];
}

object o532 : railway::Segment {
  observe railway::RailwayElement::id = [482];
  observe railway::TrackElement::monitoredBy = [@o379];
  observe railway::TrackElement::connectsTo = [@o533];
  observe railway::Segment::length = [686];
  observe railway::Segment::semaphores = [];
}

object o533 : railway::Segment {
  observe railway::RailwayElement::id = [484];
  observe railway::TrackElement::monitoredBy = [@o380];
  observe railway::TrackElement::connectsTo = [@o534];
  observe railway::Segment::length = [606];
  observe railway::Segment::semaphores = [];
}

object o534 : railway::Segment {
  observe railway::RailwayElement::id = [485];
  observe railway::TrackElement::monitoredBy = [@o380];
  observe railway::TrackElement::connectsTo = [@o535];
  observe railway::Segment::length = [672];
  observe railway::Segment::semaphores = [];
}

object o535 : railway::Segment {
  observe railway::RailwayElement::id = [486];
  observe railway::TrackElement::monitoredBy = [@o380];
  observe railway::TrackElement::connectsTo = [@o536];
  observe railway::Segment::length = [316];
  observe railway::Segment::semaphores = [];
}

object o536 : railway::Segment {
  observe railway::RailwayElement::id = [487];
  observe railway::TrackElement::monitoredBy = [@o380];
  observe railway::TrackElement::connectsTo = [@o537];
  observe railway::Segment::length = [915];
  observe railway::Segment::semaphores = [];
}

object o537 : railway::Segment {
  observe railway::RailwayElement::id = [488];
  observe railway::TrackElement::monitoredBy = [@o380];
  observe railway::TrackElement::connectsTo = [@o538];
  observe railway::Segment::length = [831];
  observe railway::Segment::semaphores = [];
}

object o538 : railway::Segment {
  observe railway::RailwayElement::id = [490];
  observe railway::TrackElement::monitoredBy = [@o381];
  observe railway::TrackElement::connectsTo = [@o539];
  observe railway::Segment::length = [711];
  observe railway::Segment::semaphores = [];
}

object o539 : railway::Segment {
  observe railway::RailwayElement::id = [491];
  observe railway::TrackElement::monitoredBy = [@o381];
  observe railway::TrackElement::connectsTo = [@o540];
  observe railway::Segment::length = [773];
  observe railway::Segment::semaphores = [];
}

object o540 : railway::Segment {
  observe railway::RailwayElement::id = [492];
  observe railway::TrackElement::monitoredBy = [@o381];
  observe railway::TrackElement::connectsTo = [@o541];
  observe railway::Segment::length = [386];
  observe railway::Segment::semaphores = [];
}

object o541 : railway::Segment {
  observe railway::RailwayElement::id = [493];
  observe railway::TrackElement::monitoredBy = [@o381];
  observe railway::TrackElement::connectsTo = [@o542];
  observe railway::Segment::length = [340];
  observe railway::Segment::semaphores = [];
}

object o542 : railway::Segment {
  observe railway::RailwayElement::id = [494];
  observe railway::TrackElement::monitoredBy = [@o381];
  observe railway::TrackElement::connectsTo = [@o543];
  observe railway::Segment::length = [597];
  observe railway::Segment::semaphores = [];
}

object o543 : railway::Segment {
  observe railway::RailwayElement::id = [496];
  observe railway::TrackElement::monitoredBy = [@o382];
  observe railway::TrackElement::connectsTo = [@o544];
  observe railway::Segment::length = [28];
  observe railway::Segment::semaphores = [];
}

object o544 : railway::Segment {
  observe railway::RailwayElement::id = [497];
  observe railway::TrackElement::monitoredBy = [@o382];
  observe railway::TrackElement::connectsTo = [@o545];
  observe railway::Segment::length = [196];
  observe railway::Segment::semaphores = [];
}

object o545 : railway::Segment {
  observe railway::RailwayElement::id = [498];
  observe railway::TrackElement::monitoredBy = [@o382];
  observe railway::TrackElement::connectsTo = [@o546];
  observe railway::Segment::length = [953];
  observe railway::Segment::semaphores = [];
}

object o546 : railway::Segment {
  observe railway::RailwayElement::id = [499];
  observe railway::TrackElement::monitoredBy = [@o382];
  observe railway::TrackElement::connectsTo = [@o547];
  observe railway::Segment::length = [473];
  observe railway::Segment::semaphores = [];
}

object o547 : railway::Segment {
  observe railway::RailwayElement::id = [500];
  observe railway::TrackElement::monitoredBy = [@o382];
  observe railway::TrackElement::connectsTo = [@o548];
  observe railway::Segment::length = [514];
  observe railway::Segment::semaphores = [];
}

object o548 : railway::Segment {
  observe railway::RailwayElement::id = [502];
  observe railway::TrackElement::monitoredBy = [@o383];
  observe railway::TrackElement::connectsTo = [@o549];
  observe railway::Segment::length = [429];
  observe railway::Segment::semaphores = [];
}

object o549 : railway::Segment {
  observe railway::RailwayElement::id = [503];
  observe railway::TrackElement::monitoredBy = [@o383];
  observe railway::TrackElement::connectsTo = [@o550];
  observe railway::Segment::length = [972];
  observe railway::Segment::semaphores = [];
}

object o550 : railway::Segment {
  observe railway::RailwayElement::id = [504];
  observe railway::TrackElement::monitoredBy = [@o383];
  observe railway::TrackElement::connectsTo = [@o551];
  observe railway::Segment::length = [708];
  observe railway::Segment::semaphores = [];
}

object o551 : railway::Segment {
  observe railway::RailwayElement::id = [505];
  observe railway::TrackElement::monitoredBy = [@o383];
  observe railway::TrackElement::connectsTo = [@o552];
  observe railway::Segment::length = [669];
  observe railway::Segment::semaphores = [];
}

object o552 : railway::Segment {
  observe railway::RailwayElement::id = [506];
  observe railway::TrackElement::monitoredBy = [@o383];
  observe railway::TrackElement::connectsTo = [@o553];
  observe railway::Segment::length = [974];
  observe railway::Segment::semaphores = [];
}

object o553 : railway::Segment {
  observe railway::RailwayElement::id = [508];
  observe railway::TrackElement::monitoredBy = [@o384];
  observe railway::TrackElement::connectsTo = [@o554];
  observe railway::Segment::length = [706];
  observe railway::Segment::semaphores = [];
}

object o554 : railway::Segment {
  observe railway::RailwayElement::id = [509];
  observe railway::TrackElement::monitoredBy = [@o384];
  observe railway::TrackElement::connectsTo = [@o555];
  observe railway::Segment::length = [35];
  observe railway::Segment::semaphores = [];
}

object o555 : railway::Segment {
  observe railway::RailwayElement::id = [510];
  observe railway::TrackElement::monitoredBy = [@o384];
  observe railway::TrackElement::connectsTo = [@o556];
  observe railway::Segment::length = [383];
  observe railway::Segment::semaphores = [];
}

object o556 : railway::Segment {
  observe railway::RailwayElement::id = [511];
  observe railway::TrackElement::monitoredBy = [@o384];
  observe railway::TrackElement::connectsTo = [@o557];
  observe railway::Segment::length = [902];
  observe railway::Segment::semaphores = [];
}

object o557 : railway::Segment {
  observe railway::RailwayElement::id = [512];
  observe railway::TrackElement::monitoredBy = [@o384];
  observe railway::TrackElement::connectsTo = [@o558];
  observe railway::Segment::length = [578];
  observe railway::Segment::semaphores = [];
}

object o558 : railway::Segment {
  observe railway::RailwayElement::id = [514];
  observe railway::TrackElement::monitoredBy = [@o385];
  observe railway::TrackElement::connectsTo = [@o559];
  observe railway::Segment::length = [630];
  observe railway::Segment::semaphores = [];
}

object o559 : railway::Segment {
  observe railway::RailwayElement::id = [515];
  observe railway::TrackElement::monitoredBy = [@o385];
  observe railway::TrackElement::connectsTo = [@o560];
  observe railway::Segment::length = [154];
  observe railway::Segment::semaphores = [];
}

object o560 : railway::Segment {
  observe railway::RailwayElement::id = [516];
  observe railway::TrackElement::monitoredBy = [@o385];
  observe railway::TrackElement::connectsTo = [@o561];
  observe railway::Segment::length = [882];
  observe railway::Segment::semaphores = [];
}

object o561 : railway::Segment {
  observe railway::RailwayElement::id = [517];
  observe railway::TrackElement::monitoredBy = [@o385];
  observe railway::TrackElement::connectsTo = [@o562];
  observe railway::Segment::length = [579];
  observe railway::Segment::semaphores = [];
}

object o562 : railway::Segment {
  observe railway::RailwayElement::id = [518];
  observe railway::TrackElement::monitoredBy = [@o385];
  observe railway::TrackElement::connectsTo = [@o563];
  observe railway::Segment::length = [19];
  observe railway::Segment::semaphores = [];
}

object o563 : railway::Segment {
  observe railway::RailwayElement::id = [520];
  observe railway::TrackElement::monitoredBy = [@o386];
  observe railway::TrackElement::connectsTo = [@o564];
  observe railway::Segment::length = [798];
  observe railway::Segment::semaphores = [];
}

object o564 : railway::Segment {
  observe railway::RailwayElement::id = [521];
  observe railway::TrackElement::monitoredBy = [@o386];
  observe railway::TrackElement::connectsTo = [@o565];
  observe railway::Segment::length = [214];
  observe railway::Segment::semaphores = [];
}

object o565 : railway::Segment {
  observe railway::RailwayElement::id = [522];
  observe railway::TrackElement::monitoredBy = [@o386];
  observe railway::TrackElement::connectsTo = [@o566];
  observe railway::Segment::length = [566];
  observe railway::Segment::semaphores = [];
}

object o566 : railway::Segment {
  observe railway::RailwayElement::id = [523];
  observe railway::TrackElement::monitoredBy = [@o386];
  observe railway::TrackElement::connectsTo = [@o567];
  observe railway::Segment::length = [441];
  observe railway::Segment::semaphores = [];
}

object o567 : railway::Segment {
  observe railway::RailwayElement::id = [524];
  observe railway::TrackElement::monitoredBy = [@o386];
  observe railway::TrackElement::connectsTo = [@o568];
  observe railway::Segment::length = [823];
  observe railway::Segment::semaphores = [];
}

object o568 : railway::Switch {
  observe railway::RailwayElement::id = [526];
  observe railway::TrackElement::monitoredBy = [@o387, @o388, @o389, @o390, @o391, @o392, @o393, @o394, @o395];
  observe railway::TrackElement::connectsTo = [@o569];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o18];
}

object o569 : railway::Segment {
  observe railway::RailwayElement::id = [528];
  observe railway::TrackElement::monitoredBy = [@o387];
  observe railway::TrackElement::connectsTo = [@o570];
  observe railway::Segment::length = [868];
  observe railway::Segment::semaphores = [];
}

object o570 : railway::Segment {
  observe railway::RailwayElement::id = [529];
  observe railway::TrackElement::monitoredBy = [@o387];
  observe railway::TrackElement::connectsTo = [@o571];
  observe railway::Segment::length = [182];
  observe railway::Segment::semaphores = [];
}

object o571 : railway::Segment {
  observe railway::RailwayElement::id = [530];
  observe railway::TrackElement::monitoredBy = [@o387];
  observe railway::TrackElement::connectsTo = [@o572];
  observe railway::Segment::length = [241];
  observe railway::Segment::semaphores = [];
}

object o572 : railway::Segment {
  observe railway::RailwayElement::id = [531];
  observe railway::TrackElement::monitoredBy = [@o387];
  observe railway::TrackElement::connectsTo = [@o573];
  observe railway::Segment::length = [734];
  observe railway::Segment::semaphores = [];
}

object o573 : railway::Segment {
  observe railway::RailwayElement::id = [532];
  observe railway::TrackElement::monitoredBy = [@o387];
  observe railway::TrackElement::connectsTo = [@o574];
  observe railway::Segment::length = [70];
  observe railway::Segment::semaphores = [];
}

object o574 : railway::Segment {
  observe railway::RailwayElement::id = [534];
  observe railway::TrackElement::monitoredBy = [@o388];
  observe railway::TrackElement::connectsTo = [@o575];
  observe railway::Segment::length = [665];
  observe railway::Segment::semaphores = [];
}

object o575 : railway::Segment {
  observe railway::RailwayElement::id = [535];
  observe railway::TrackElement::monitoredBy = [@o388];
  observe railway::TrackElement::connectsTo = [@o576];
  observe railway::Segment::length = [860];
  observe railway::Segment::semaphores = [];
}

object o576 : railway::Segment {
  observe railway::RailwayElement::id = [536];
  observe railway::TrackElement::monitoredBy = [@o388];
  observe railway::TrackElement::connectsTo = [@o577];
  observe railway::Segment::length = [143];
  observe railway::Segment::semaphores = [];
}

object o577 : railway::Segment {
  observe railway::RailwayElement::id = [537];
  observe railway::TrackElement::monitoredBy = [@o388];
  observe railway::TrackElement::connectsTo = [@o578];
  observe railway::Segment::length = [962];
  observe railway::Segment::semaphores = [];
}

object o578 : railway::Segment {
  observe railway::RailwayElement::id = [538];
  observe railway::TrackElement::monitoredBy = [@o388];
  observe railway::TrackElement::connectsTo = [@o579];
  observe railway::Segment::length = [346];
  observe railway::Segment::semaphores = [];
}

object o579 : railway::Segment {
  observe railway::RailwayElement::id = [540];
  observe railway::TrackElement::monitoredBy = [@o389];
  observe railway::TrackElement::connectsTo = [@o580];
  observe railway::Segment::length = [417];
  observe railway::Segment::semaphores = [];
}

object o580 : railway::Segment {
  observe railway::RailwayElement::id = [541];
  observe railway::TrackElement::monitoredBy = [@o389];
  observe railway::TrackElement::connectsTo = [@o581];
  observe railway::Segment::length = [630];
  observe railway::Segment::semaphores = [];
}

object o581 : railway::Segment {
  observe railway::RailwayElement::id = [542];
  observe railway::TrackElement::monitoredBy = [@o389];
  observe railway::TrackElement::connectsTo = [@o582];
  observe railway::Segment::length = [106];
  observe railway::Segment::semaphores = [];
}

object o582 : railway::Segment {
  observe railway::RailwayElement::id = [543];
  observe railway::TrackElement::monitoredBy = [@o389];
  observe railway::TrackElement::connectsTo = [@o583];
  observe railway::Segment::length = [482];
  observe railway::Segment::semaphores = [];
}

object o583 : railway::Segment {
  observe railway::RailwayElement::id = [544];
  observe railway::TrackElement::monitoredBy = [@o389];
  observe railway::TrackElement::connectsTo = [@o584];
  observe railway::Segment::length = [560];
  observe railway::Segment::semaphores = [];
}

object o584 : railway::Segment {
  observe railway::RailwayElement::id = [546];
  observe railway::TrackElement::monitoredBy = [@o390];
  observe railway::TrackElement::connectsTo = [@o585];
  observe railway::Segment::length = [135];
  observe railway::Segment::semaphores = [];
}

object o585 : railway::Segment {
  observe railway::RailwayElement::id = [547];
  observe railway::TrackElement::monitoredBy = [@o390];
  observe railway::TrackElement::connectsTo = [@o586];
  observe railway::Segment::length = [395];
  observe railway::Segment::semaphores = [];
}

object o586 : railway::Segment {
  observe railway::RailwayElement::id = [548];
  observe railway::TrackElement::monitoredBy = [@o390];
  observe railway::TrackElement::connectsTo = [@o587];
  observe railway::Segment::length = [950];
  observe railway::Segment::semaphores = [];
}

object o587 : railway::Segment {
  observe railway::RailwayElement::id = [549];
  observe railway::TrackElement::monitoredBy = [@o390];
  observe railway::TrackElement::connectsTo = [@o588];
  observe railway::Segment::length = [569];
  observe railway::Segment::semaphores = [];
}

object o588 : railway::Segment {
  observe railway::RailwayElement::id = [550];
  observe railway::TrackElement::monitoredBy = [@o390];
  observe railway::TrackElement::connectsTo = [@o589];
  observe railway::Segment::length = [452];
  observe railway::Segment::semaphores = [];
}

object o589 : railway::Segment {
  observe railway::RailwayElement::id = [552];
  observe railway::TrackElement::monitoredBy = [@o391];
  observe railway::TrackElement::connectsTo = [@o590];
  observe railway::Segment::length = [744];
  observe railway::Segment::semaphores = [];
}

object o590 : railway::Segment {
  observe railway::RailwayElement::id = [553];
  observe railway::TrackElement::monitoredBy = [@o391];
  observe railway::TrackElement::connectsTo = [@o591];
  observe railway::Segment::length = [702];
  observe railway::Segment::semaphores = [];
}

object o591 : railway::Segment {
  observe railway::RailwayElement::id = [554];
  observe railway::TrackElement::monitoredBy = [@o391];
  observe railway::TrackElement::connectsTo = [@o592];
  observe railway::Segment::length = [68];
  observe railway::Segment::semaphores = [];
}

object o592 : railway::Segment {
  observe railway::RailwayElement::id = [555];
  observe railway::TrackElement::monitoredBy = [@o391];
  observe railway::TrackElement::connectsTo = [@o593];
  observe railway::Segment::length = [634];
  observe railway::Segment::semaphores = [];
}

object o593 : railway::Segment {
  observe railway::RailwayElement::id = [556];
  observe railway::TrackElement::monitoredBy = [@o391];
  observe railway::TrackElement::connectsTo = [@o594];
  observe railway::Segment::length = [852];
  observe railway::Segment::semaphores = [];
}

object o594 : railway::Segment {
  observe railway::RailwayElement::id = [558];
  observe railway::TrackElement::monitoredBy = [@o392];
  observe railway::TrackElement::connectsTo = [@o595];
  observe railway::Segment::length = [551];
  observe railway::Segment::semaphores = [];
}

object o595 : railway::Segment {
  observe railway::RailwayElement::id = [559];
  observe railway::TrackElement::monitoredBy = [@o392];
  observe railway::TrackElement::connectsTo = [@o596];
  observe railway::Segment::length = [875];
  observe railway::Segment::semaphores = [];
}

object o596 : railway::Segment {
  observe railway::RailwayElement::id = [560];
  observe railway::TrackElement::monitoredBy = [@o392];
  observe railway::TrackElement::connectsTo = [@o597];
  observe railway::Segment::length = [989];
  observe railway::Segment::semaphores = [];
}

object o597 : railway::Segment {
  observe railway::RailwayElement::id = [561];
  observe railway::TrackElement::monitoredBy = [@o392];
  observe railway::TrackElement::connectsTo = [@o598];
  observe railway::Segment::length = [837];
  observe railway::Segment::semaphores = [];
}

object o598 : railway::Segment {
  observe railway::RailwayElement::id = [562];
  observe railway::TrackElement::monitoredBy = [@o392];
  observe railway::TrackElement::connectsTo = [@o599];
  observe railway::Segment::length = [252];
  observe railway::Segment::semaphores = [];
}

object o599 : railway::Segment {
  observe railway::RailwayElement::id = [564];
  observe railway::TrackElement::monitoredBy = [@o393];
  observe railway::TrackElement::connectsTo = [@o600];
  observe railway::Segment::length = [77];
  observe railway::Segment::semaphores = [];
}

object o600 : railway::Segment {
  observe railway::RailwayElement::id = [565];
  observe railway::TrackElement::monitoredBy = [@o393];
  observe railway::TrackElement::connectsTo = [@o601];
  observe railway::Segment::length = [710];
  observe railway::Segment::semaphores = [];
}

object o601 : railway::Segment {
  observe railway::RailwayElement::id = [566];
  observe railway::TrackElement::monitoredBy = [@o393];
  observe railway::TrackElement::connectsTo = [@o602];
  observe railway::Segment::length = [845];
  observe railway::Segment::semaphores = [];
}

object o602 : railway::Segment {
  observe railway::RailwayElement::id = [567];
  observe railway::TrackElement::monitoredBy = [@o393];
  observe railway::TrackElement::connectsTo = [@o603];
  observe railway::Segment::length = [835];
  observe railway::Segment::semaphores = [];
}

object o603 : railway::Segment {
  observe railway::RailwayElement::id = [568];
  observe railway::TrackElement::monitoredBy = [@o393];
  observe railway::TrackElement::connectsTo = [@o604];
  observe railway::Segment::length = [27];
  observe railway::Segment::semaphores = [];
}

object o604 : railway::Segment {
  observe railway::RailwayElement::id = [570];
  observe railway::TrackElement::monitoredBy = [@o394];
  observe railway::TrackElement::connectsTo = [@o605];
  observe railway::Segment::length = [686];
  observe railway::Segment::semaphores = [];
}

object o605 : railway::Segment {
  observe railway::RailwayElement::id = [571];
  observe railway::TrackElement::monitoredBy = [@o394];
  observe railway::TrackElement::connectsTo = [@o606];
  observe railway::Segment::length = [247];
  observe railway::Segment::semaphores = [];
}

object o606 : railway::Segment {
  observe railway::RailwayElement::id = [572];
  observe railway::TrackElement::monitoredBy = [@o394];
  observe railway::TrackElement::connectsTo = [@o607];
  observe railway::Segment::length = [348];
  observe railway::Segment::semaphores = [];
}

object o607 : railway::Segment {
  observe railway::RailwayElement::id = [573];
  observe railway::TrackElement::monitoredBy = [@o394];
  observe railway::TrackElement::connectsTo = [@o608];
  observe railway::Segment::length = [206];
  observe railway::Segment::semaphores = [];
}

object o608 : railway::Segment {
  observe railway::RailwayElement::id = [574];
  observe railway::TrackElement::monitoredBy = [@o394];
  observe railway::TrackElement::connectsTo = [@o609];
  observe railway::Segment::length = [391];
  observe railway::Segment::semaphores = [];
}

object o609 : railway::Segment {
  observe railway::RailwayElement::id = [576];
  observe railway::TrackElement::monitoredBy = [@o395];
  observe railway::TrackElement::connectsTo = [@o610];
  observe railway::Segment::length = [911];
  observe railway::Segment::semaphores = [];
}

object o610 : railway::Segment {
  observe railway::RailwayElement::id = [577];
  observe railway::TrackElement::monitoredBy = [@o395];
  observe railway::TrackElement::connectsTo = [@o611];
  observe railway::Segment::length = [394];
  observe railway::Segment::semaphores = [];
}

object o611 : railway::Segment {
  observe railway::RailwayElement::id = [578];
  observe railway::TrackElement::monitoredBy = [@o395];
  observe railway::TrackElement::connectsTo = [@o612];
  observe railway::Segment::length = [268];
  observe railway::Segment::semaphores = [];
}

object o612 : railway::Segment {
  observe railway::RailwayElement::id = [579];
  observe railway::TrackElement::monitoredBy = [@o395];
  observe railway::TrackElement::connectsTo = [@o613];
  observe railway::Segment::length = [468];
  observe railway::Segment::semaphores = [];
}

object o613 : railway::Segment {
  observe railway::RailwayElement::id = [580];
  observe railway::TrackElement::monitoredBy = [@o395];
  observe railway::TrackElement::connectsTo = [@o614];
  observe railway::Segment::length = [781];
  observe railway::Segment::semaphores = [];
}

object o614 : railway::Switch {
  observe railway::RailwayElement::id = [582];
  observe railway::TrackElement::monitoredBy = [@o396, @o397, @o398, @o399, @o400];
  observe railway::TrackElement::connectsTo = [@o615];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o19];
}

object o615 : railway::Segment {
  observe railway::RailwayElement::id = [584];
  observe railway::TrackElement::monitoredBy = [@o396];
  observe railway::TrackElement::connectsTo = [@o616];
  observe railway::Segment::length = [666];
  observe railway::Segment::semaphores = [];
}

object o616 : railway::Segment {
  observe railway::RailwayElement::id = [585];
  observe railway::TrackElement::monitoredBy = [@o396];
  observe railway::TrackElement::connectsTo = [@o617];
  observe railway::Segment::length = [464];
  observe railway::Segment::semaphores = [];
}

object o617 : railway::Segment {
  observe railway::RailwayElement::id = [586];
  observe railway::TrackElement::monitoredBy = [@o396];
  observe railway::TrackElement::connectsTo = [@o618];
  observe railway::Segment::length = [375];
  observe railway::Segment::semaphores = [];
}

object o618 : railway::Segment {
  observe railway::RailwayElement::id = [587];
  observe railway::TrackElement::monitoredBy = [@o396];
  observe railway::TrackElement::connectsTo = [@o619];
  observe railway::Segment::length = [825];
  observe railway::Segment::semaphores = [];
}

object o619 : railway::Segment {
  observe railway::RailwayElement::id = [588];
  observe railway::TrackElement::monitoredBy = [@o396];
  observe railway::TrackElement::connectsTo = [@o620];
  observe railway::Segment::length = [741];
  observe railway::Segment::semaphores = [];
}

object o620 : railway::Segment {
  observe railway::RailwayElement::id = [590];
  observe railway::TrackElement::monitoredBy = [@o397];
  observe railway::TrackElement::connectsTo = [@o621];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [];
}

object o621 : railway::Segment {
  observe railway::RailwayElement::id = [591];
  observe railway::TrackElement::monitoredBy = [@o397];
  observe railway::TrackElement::connectsTo = [@o622];
  observe railway::Segment::length = [420];
  observe railway::Segment::semaphores = [];
}

object o622 : railway::Segment {
  observe railway::RailwayElement::id = [592];
  observe railway::TrackElement::monitoredBy = [@o397];
  observe railway::TrackElement::connectsTo = [@o623];
  observe railway::Segment::length = [855];
  observe railway::Segment::semaphores = [];
}

object o623 : railway::Segment {
  observe railway::RailwayElement::id = [593];
  observe railway::TrackElement::monitoredBy = [@o397];
  observe railway::TrackElement::connectsTo = [@o624];
  observe railway::Segment::length = [856];
  observe railway::Segment::semaphores = [];
}

object o624 : railway::Segment {
  observe railway::RailwayElement::id = [594];
  observe railway::TrackElement::monitoredBy = [@o397];
  observe railway::TrackElement::connectsTo = [@o625];
  observe railway::Segment::length = [320];
  observe railway::Segment::semaphores = [];
}

object o625 : railway::Segment {
  observe railway::RailwayElement::id = [596];
  observe railway::TrackElement::monitoredBy = [@o398];
  observe railway::TrackElement::connectsTo = [@o626];
  observe railway::Segment::length = [78];
  observe railway::Segment::semaphores = [];
}

object o626 : railway::Segment {
  observe railway::RailwayElement::id = [597];
  observe railway::TrackElement::monitoredBy = [@o398];
  observe railway::TrackElement::connectsTo = [@o627];
  observe railway::Segment::length = [58];
  observe railway::Segment::semaphores = [];
}

object o627 : railway::Segment {
  observe railway::RailwayElement::id = [598];
  observe railway::TrackElement::monitoredBy = [@o398];
  observe railway::TrackElement::connectsTo = [@o628];
  observe railway::Segment::length = [959];
  observe railway::Segment::semaphores = [];
}

object o628 : railway::Segment {
  observe railway::RailwayElement::id = [599];
  observe railway::TrackElement::monitoredBy = [@o398];
  observe railway::TrackElement::connectsTo = [@o629];
  observe railway::Segment::length = [633];
  observe railway::Segment::semaphores = [];
}

object o629 : railway::Segment {
  observe railway::RailwayElement::id = [600];
  observe railway::TrackElement::monitoredBy = [@o398];
  observe railway::TrackElement::connectsTo = [@o630];
  observe railway::Segment::length = [244];
  observe railway::Segment::semaphores = [];
}

object o630 : railway::Segment {
  observe railway::RailwayElement::id = [602];
  observe railway::TrackElement::monitoredBy = [@o399];
  observe railway::TrackElement::connectsTo = [@o631];
  observe railway::Segment::length = [830];
  observe railway::Segment::semaphores = [];
}

object o631 : railway::Segment {
  observe railway::RailwayElement::id = [603];
  observe railway::TrackElement::monitoredBy = [@o399];
  observe railway::TrackElement::connectsTo = [@o632];
  observe railway::Segment::length = [40];
  observe railway::Segment::semaphores = [];
}

object o632 : railway::Segment {
  observe railway::RailwayElement::id = [604];
  observe railway::TrackElement::monitoredBy = [@o399];
  observe railway::TrackElement::connectsTo = [@o633];
  observe railway::Segment::length = [534];
  observe railway::Segment::semaphores = [];
}

object o633 : railway::Segment {
  observe railway::RailwayElement::id = [605];
  observe railway::TrackElement::monitoredBy = [@o399];
  observe railway::TrackElement::connectsTo = [@o634];
  observe railway::Segment::length = [945];
  observe railway::Segment::semaphores = [];
}

object o634 : railway::Segment {
  observe railway::RailwayElement::id = [606];
  observe railway::TrackElement::monitoredBy = [@o399];
  observe railway::TrackElement::connectsTo = [@o635];
  observe railway::Segment::length = [997];
  observe railway::Segment::semaphores = [];
}

object o635 : railway::Segment {
  observe railway::RailwayElement::id = [608];
  observe railway::TrackElement::monitoredBy = [@o400];
  observe railway::TrackElement::connectsTo = [@o636];
  observe railway::Segment::length = [142];
  observe railway::Segment::semaphores = [];
}

object o636 : railway::Segment {
  observe railway::RailwayElement::id = [609];
  observe railway::TrackElement::monitoredBy = [@o400];
  observe railway::TrackElement::connectsTo = [@o637];
  observe railway::Segment::length = [275];
  observe railway::Segment::semaphores = [];
}

object o637 : railway::Segment {
  observe railway::RailwayElement::id = [610];
  observe railway::TrackElement::monitoredBy = [@o400];
  observe railway::TrackElement::connectsTo = [@o638];
  observe railway::Segment::length = [382];
  observe railway::Segment::semaphores = [];
}

object o638 : railway::Segment {
  observe railway::RailwayElement::id = [611];
  observe railway::TrackElement::monitoredBy = [@o400];
  observe railway::TrackElement::connectsTo = [@o639];
  observe railway::Segment::length = [557];
  observe railway::Segment::semaphores = [];
}

object o639 : railway::Segment {
  observe railway::RailwayElement::id = [612];
  observe railway::TrackElement::monitoredBy = [@o400];
  observe railway::TrackElement::connectsTo = [@o640];
  observe railway::Segment::length = [165];
  observe railway::Segment::semaphores = [];
}

object o640 : railway::Switch {
  observe railway::RailwayElement::id = [614];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o641];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@o20];
}

object o641 : railway::Segment {
  observe railway::RailwayElement::id = [616];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o642];
  observe railway::Segment::length = [205];
  observe railway::Segment::semaphores = [];
}

object o642 : railway::Segment {
  observe railway::RailwayElement::id = [617];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o643];
  observe railway::Segment::length = [144];
  observe railway::Segment::semaphores = [];
}

object o643 : railway::Segment {
  observe railway::RailwayElement::id = [618];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o644];
  observe railway::Segment::length = [770];
  observe railway::Segment::semaphores = [];
}

object o644 : railway::Segment {
  observe railway::RailwayElement::id = [619];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o645];
  observe railway::Segment::length = [113];
  observe railway::Segment::semaphores = [];
}

object o645 : railway::Segment {
  observe railway::RailwayElement::id = [620];
  observe railway::TrackElement::monitoredBy = [@o401];
  observe railway::TrackElement::connectsTo = [@o646];
  observe railway::Segment::length = [575];
  observe railway::Segment::semaphores = [];
}

object o646 : railway::Switch {
  observe railway::RailwayElement::id = [622];
  observe railway::TrackElement::monitoredBy = [@o402, @o403, @o404, @o405, @o406, @o407, @o408, @o409, @o410];
  observe railway::TrackElement::connectsTo = [@o647];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o21];
}

object o647 : railway::Segment {
  observe railway::RailwayElement::id = [624];
  observe railway::TrackElement::monitoredBy = [@o402];
  observe railway::TrackElement::connectsTo = [@o648];
  observe railway::Segment::length = [452];
  observe railway::Segment::semaphores = [];
}

object o648 : railway::Segment {
  observe railway::RailwayElement::id = [625];
  observe railway::TrackElement::monitoredBy = [@o402];
  observe railway::TrackElement::connectsTo = [@o649];
  observe railway::Segment::length = [900];
  observe railway::Segment::semaphores = [];
}

object o649 : railway::Segment {
  observe railway::RailwayElement::id = [626];
  observe railway::TrackElement::monitoredBy = [@o402];
  observe railway::TrackElement::connectsTo = [@o650];
  observe railway::Segment::length = [552];
  observe railway::Segment::semaphores = [];
}

object o650 : railway::Segment {
  observe railway::RailwayElement::id = [627];
  observe railway::TrackElement::monitoredBy = [@o402];
  observe railway::TrackElement::connectsTo = [@o651];
  observe railway::Segment::length = [411];
  observe railway::Segment::semaphores = [];
}

object o651 : railway::Segment {
  observe railway::RailwayElement::id = [628];
  observe railway::TrackElement::monitoredBy = [@o402];
  observe railway::TrackElement::connectsTo = [@o652];
  observe railway::Segment::length = [664];
  observe railway::Segment::semaphores = [];
}

object o652 : railway::Segment {
  observe railway::RailwayElement::id = [630];
  observe railway::TrackElement::monitoredBy = [@o403];
  observe railway::TrackElement::connectsTo = [@o653];
  observe railway::Segment::length = [453];
  observe railway::Segment::semaphores = [];
}

object o653 : railway::Segment {
  observe railway::RailwayElement::id = [631];
  observe railway::TrackElement::monitoredBy = [@o403];
  observe railway::TrackElement::connectsTo = [@o654];
  observe railway::Segment::length = [599];
  observe railway::Segment::semaphores = [];
}

object o654 : railway::Segment {
  observe railway::RailwayElement::id = [632];
  observe railway::TrackElement::monitoredBy = [@o403];
  observe railway::TrackElement::connectsTo = [@o655];
  observe railway::Segment::length = [616];
  observe railway::Segment::semaphores = [];
}

object o655 : railway::Segment {
  observe railway::RailwayElement::id = [633];
  observe railway::TrackElement::monitoredBy = [@o403];
  observe railway::TrackElement::connectsTo = [@o656];
  observe railway::Segment::length = [714];
  observe railway::Segment::semaphores = [];
}

object o656 : railway::Segment {
  observe railway::RailwayElement::id = [634];
  observe railway::TrackElement::monitoredBy = [@o403];
  observe railway::TrackElement::connectsTo = [@o657];
  observe railway::Segment::length = [758];
  observe railway::Segment::semaphores = [];
}

object o657 : railway::Segment {
  observe railway::RailwayElement::id = [636];
  observe railway::TrackElement::monitoredBy = [@o404];
  observe railway::TrackElement::connectsTo = [@o658];
  observe railway::Segment::length = [357];
  observe railway::Segment::semaphores = [];
}

object o658 : railway::Segment {
  observe railway::RailwayElement::id = [637];
  observe railway::TrackElement::monitoredBy = [@o404];
  observe railway::TrackElement::connectsTo = [@o659];
  observe railway::Segment::length = [604];
  observe railway::Segment::semaphores = [];
}

object o659 : railway::Segment {
  observe railway::RailwayElement::id = [638];
  observe railway::TrackElement::monitoredBy = [@o404];
  observe railway::TrackElement::connectsTo = [@o660];
  observe railway::Segment::length = [492];
  observe railway::Segment::semaphores = [];
}

object o660 : railway::Segment {
  observe railway::RailwayElement::id = [639];
  observe railway::TrackElement::monitoredBy = [@o404];
  observe railway::TrackElement::connectsTo = [@o661];
  observe railway::Segment::length = [37];
  observe railway::Segment::semaphores = [];
}

object o661 : railway::Segment {
  observe railway::RailwayElement::id = [640];
  observe railway::TrackElement::monitoredBy = [@o404];
  observe railway::TrackElement::connectsTo = [@o662];
  observe railway::Segment::length = [427];
  observe railway::Segment::semaphores = [];
}

object o662 : railway::Segment {
  observe railway::RailwayElement::id = [642];
  observe railway::TrackElement::monitoredBy = [@o405];
  observe railway::TrackElement::connectsTo = [@o663];
  observe railway::Segment::length = [881];
  observe railway::Segment::semaphores = [];
}

object o663 : railway::Segment {
  observe railway::RailwayElement::id = [643];
  observe railway::TrackElement::monitoredBy = [@o405];
  observe railway::TrackElement::connectsTo = [@o664];
  observe railway::Segment::length = [902];
  observe railway::Segment::semaphores = [];
}

object o664 : railway::Segment {
  observe railway::RailwayElement::id = [644];
  observe railway::TrackElement::monitoredBy = [@o405];
  observe railway::TrackElement::connectsTo = [@o665];
  observe railway::Segment::length = [47];
  observe railway::Segment::semaphores = [];
}

object o665 : railway::Segment {
  observe railway::RailwayElement::id = [645];
  observe railway::TrackElement::monitoredBy = [@o405];
  observe railway::TrackElement::connectsTo = [@o666];
  observe railway::Segment::length = [195];
  observe railway::Segment::semaphores = [];
}

object o666 : railway::Segment {
  observe railway::RailwayElement::id = [646];
  observe railway::TrackElement::monitoredBy = [@o405];
  observe railway::TrackElement::connectsTo = [@o667];
  observe railway::Segment::length = [735];
  observe railway::Segment::semaphores = [];
}

object o667 : railway::Segment {
  observe railway::RailwayElement::id = [648];
  observe railway::TrackElement::monitoredBy = [@o406];
  observe railway::TrackElement::connectsTo = [@o668];
  observe railway::Segment::length = [942];
  observe railway::Segment::semaphores = [];
}

object o668 : railway::Segment {
  observe railway::RailwayElement::id = [649];
  observe railway::TrackElement::monitoredBy = [@o406];
  observe railway::TrackElement::connectsTo = [@o669];
  observe railway::Segment::length = [403];
  observe railway::Segment::semaphores = [];
}

object o669 : railway::Segment {
  observe railway::RailwayElement::id = [650];
  observe railway::TrackElement::monitoredBy = [@o406];
  observe railway::TrackElement::connectsTo = [@o670];
  observe railway::Segment::length = [615];
  observe railway::Segment::semaphores = [];
}

object o670 : railway::Segment {
  observe railway::RailwayElement::id = [651];
  observe railway::TrackElement::monitoredBy = [@o406];
  observe railway::TrackElement::connectsTo = [@o671];
  observe railway::Segment::length = [887];
  observe railway::Segment::semaphores = [];
}

object o671 : railway::Segment {
  observe railway::RailwayElement::id = [652];
  observe railway::TrackElement::monitoredBy = [@o406];
  observe railway::TrackElement::connectsTo = [@o672];
  observe railway::Segment::length = [387];
  observe railway::Segment::semaphores = [];
}

object o672 : railway::Segment {
  observe railway::RailwayElement::id = [654];
  observe railway::TrackElement::monitoredBy = [@o407];
  observe railway::TrackElement::connectsTo = [@o673];
  observe railway::Segment::length = [285];
  observe railway::Segment::semaphores = [];
}

object o673 : railway::Segment {
  observe railway::RailwayElement::id = [655];
  observe railway::TrackElement::monitoredBy = [@o407];
  observe railway::TrackElement::connectsTo = [@o674];
  observe railway::Segment::length = [889];
  observe railway::Segment::semaphores = [];
}

object o674 : railway::Segment {
  observe railway::RailwayElement::id = [656];
  observe railway::TrackElement::monitoredBy = [@o407];
  observe railway::TrackElement::connectsTo = [@o675];
  observe railway::Segment::length = [87];
  observe railway::Segment::semaphores = [];
}

object o675 : railway::Segment {
  observe railway::RailwayElement::id = [657];
  observe railway::TrackElement::monitoredBy = [@o407];
  observe railway::TrackElement::connectsTo = [@o676];
  observe railway::Segment::length = [271];
  observe railway::Segment::semaphores = [];
}

object o676 : railway::Segment {
  observe railway::RailwayElement::id = [658];
  observe railway::TrackElement::monitoredBy = [@o407];
  observe railway::TrackElement::connectsTo = [@o677];
  observe railway::Segment::length = [432];
  observe railway::Segment::semaphores = [];
}

object o677 : railway::Segment {
  observe railway::RailwayElement::id = [660];
  observe railway::TrackElement::monitoredBy = [@o408];
  observe railway::TrackElement::connectsTo = [@o678];
  observe railway::Segment::length = [11];
  observe railway::Segment::semaphores = [];
}

object o678 : railway::Segment {
  observe railway::RailwayElement::id = [661];
  observe railway::TrackElement::monitoredBy = [@o408];
  observe railway::TrackElement::connectsTo = [@o679];
  observe railway::Segment::length = [153];
  observe railway::Segment::semaphores = [];
}

object o679 : railway::Segment {
  observe railway::RailwayElement::id = [662];
  observe railway::TrackElement::monitoredBy = [@o408];
  observe railway::TrackElement::connectsTo = [@o680];
  observe railway::Segment::length = [444];
  observe railway::Segment::semaphores = [];
}

object o680 : railway::Segment {
  observe railway::RailwayElement::id = [663];
  observe railway::TrackElement::monitoredBy = [@o408];
  observe railway::TrackElement::connectsTo = [@o681];
  observe railway::Segment::length = [576];
  observe railway::Segment::semaphores = [];
}

object o681 : railway::Segment {
  observe railway::RailwayElement::id = [664];
  observe railway::TrackElement::monitoredBy = [@o408];
  observe railway::TrackElement::connectsTo = [@o682];
  observe railway::Segment::length = [11];
  observe railway::Segment::semaphores = [];
}

object o682 : railway::Segment {
  observe railway::RailwayElement::id = [666];
  observe railway::TrackElement::monitoredBy = [@o409];
  observe railway::TrackElement::connectsTo = [@o683];
  observe railway::Segment::length = [229];
  observe railway::Segment::semaphores = [];
}

object o683 : railway::Segment {
  observe railway::RailwayElement::id = [667];
  observe railway::TrackElement::monitoredBy = [@o409];
  observe railway::TrackElement::connectsTo = [@o684];
  observe railway::Segment::length = [541];
  observe railway::Segment::semaphores = [];
}

object o684 : railway::Segment {
  observe railway::RailwayElement::id = [668];
  observe railway::TrackElement::monitoredBy = [@o409];
  observe railway::TrackElement::connectsTo = [@o685];
  observe railway::Segment::length = [924];
  observe railway::Segment::semaphores = [];
}

object o685 : railway::Segment {
  observe railway::RailwayElement::id = [669];
  observe railway::TrackElement::monitoredBy = [@o409];
  observe railway::TrackElement::connectsTo = [@o686];
  observe railway::Segment::length = [801];
  observe railway::Segment::semaphores = [];
}

object o686 : railway::Segment {
  observe railway::RailwayElement::id = [670];
  observe railway::TrackElement::monitoredBy = [@o409];
  observe railway::TrackElement::connectsTo = [@o687];
  observe railway::Segment::length = [887];
  observe railway::Segment::semaphores = [];
}

object o687 : railway::Segment {
  observe railway::RailwayElement::id = [672];
  observe railway::TrackElement::monitoredBy = [@o410];
  observe railway::TrackElement::connectsTo = [@o688];
  observe railway::Segment::length = [66];
  observe railway::Segment::semaphores = [];
}

object o688 : railway::Segment {
  observe railway::RailwayElement::id = [673];
  observe railway::TrackElement::monitoredBy = [@o410];
  observe railway::TrackElement::connectsTo = [@o689];
  observe railway::Segment::length = [898];
  observe railway::Segment::semaphores = [];
}

object o689 : railway::Segment {
  observe railway::RailwayElement::id = [674];
  observe railway::TrackElement::monitoredBy = [@o410];
  observe railway::TrackElement::connectsTo = [@o690];
  observe railway::Segment::length = [660];
  observe railway::Segment::semaphores = [];
}

object o690 : railway::Segment {
  observe railway::RailwayElement::id = [675];
  observe railway::TrackElement::monitoredBy = [@o410];
  observe railway::TrackElement::connectsTo = [@o691];
  observe railway::Segment::length = [555];
  observe railway::Segment::semaphores = [];
}

object o691 : railway::Segment {
  observe railway::RailwayElement::id = [676];
  observe railway::TrackElement::monitoredBy = [@o410];
  observe railway::TrackElement::connectsTo = [@o692];
  observe railway::Segment::length = [559];
  observe railway::Segment::semaphores = [];
}

object o692 : railway::Switch {
  observe railway::RailwayElement::id = [678];
  observe railway::TrackElement::monitoredBy = [@o411, @o412, @o413, @o414, @o415, @o416, @o417];
  observe railway::TrackElement::connectsTo = [@o693];
  observe railway::Switch::currentPosition = [railway::Position::DIVERGING];
  observe railway::Switch::positions = [@o22];
}

object o693 : railway::Segment {
  observe railway::RailwayElement::id = [680];
  observe railway::TrackElement::monitoredBy = [@o411];
  observe railway::TrackElement::connectsTo = [@o694];
  observe railway::Segment::length = [734];
  observe railway::Segment::semaphores = [];
}

object o694 : railway::Segment {
  observe railway::RailwayElement::id = [681];
  observe railway::TrackElement::monitoredBy = [@o411];
  observe railway::TrackElement::connectsTo = [@o695];
  observe railway::Segment::length = [720];
  observe railway::Segment::semaphores = [];
}

object o695 : railway::Segment {
  observe railway::RailwayElement::id = [682];
  observe railway::TrackElement::monitoredBy = [@o411];
  observe railway::TrackElement::connectsTo = [@o696];
  observe railway::Segment::length = [382];
  observe railway::Segment::semaphores = [];
}

object o696 : railway::Segment {
  observe railway::RailwayElement::id = [683];
  observe railway::TrackElement::monitoredBy = [@o411];
  observe railway::TrackElement::connectsTo = [@o697];
  observe railway::Segment::length = [79];
  observe railway::Segment::semaphores = [];
}

object o697 : railway::Segment {
  observe railway::RailwayElement::id = [684];
  observe railway::TrackElement::monitoredBy = [@o411];
  observe railway::TrackElement::connectsTo = [@o698];
  observe railway::Segment::length = [538];
  observe railway::Segment::semaphores = [];
}

object o698 : railway::Segment {
  observe railway::RailwayElement::id = [686];
  observe railway::TrackElement::monitoredBy = [@o412];
  observe railway::TrackElement::connectsTo = [@o699];
  observe railway::Segment::length = [618];
  observe railway::Segment::semaphores = [];
}

object o699 : railway::Segment {
  observe railway::RailwayElement::id = [687];
  observe railway::TrackElement::monitoredBy = [@o412];
  observe railway::TrackElement::connectsTo = [@o700];
  observe railway::Segment::length = [132];
  observe railway::Segment::semaphores = [];
}

object o700 : railway::Segment {
  observe railway::RailwayElement::id = [688];
  observe railway::TrackElement::monitoredBy = [@o412];
  observe railway::TrackElement::connectsTo = [@o701];
  observe railway::Segment::length = [133];
  observe railway::Segment::semaphores = [];
}

object o701 : railway::Segment {
  observe railway::RailwayElement::id = [689];
  observe railway::TrackElement::monitoredBy = [@o412];
  observe railway::TrackElement::connectsTo = [@o702];
  observe railway::Segment::length = [108];
  observe railway::Segment::semaphores = [];
}

object o702 : railway::Segment {
  observe railway::RailwayElement::id = [690];
  observe railway::TrackElement::monitoredBy = [@o412];
  observe railway::TrackElement::connectsTo = [@o703];
  observe railway::Segment::length = [563];
  observe railway::Segment::semaphores = [];
}

object o703 : railway::Segment {
  observe railway::RailwayElement::id = [692];
  observe railway::TrackElement::monitoredBy = [@o413];
  observe railway::TrackElement::connectsTo = [@o704];
  observe railway::Segment::length = [81];
  observe railway::Segment::semaphores = [];
}

object o704 : railway::Segment {
  observe railway::RailwayElement::id = [693];
  observe railway::TrackElement::monitoredBy = [@o413];
  observe railway::TrackElement::connectsTo = [@o705];
  observe railway::Segment::length = [832];
  observe railway::Segment::semaphores = [];
}

object o705 : railway::Segment {
  observe railway::RailwayElement::id = [694];
  observe railway::TrackElement::monitoredBy = [@o413];
  observe railway::TrackElement::connectsTo = [@o706];
  observe railway::Segment::length = [45];
  observe railway::Segment::semaphores = [];
}

object o706 : railway::Segment {
  observe railway::RailwayElement::id = [695];
  observe railway::TrackElement::monitoredBy = [@o413];
  observe railway::TrackElement::connectsTo = [@o707];
  observe railway::Segment::length = [843];
  observe railway::Segment::semaphores = [];
}

object o707 : railway::Segment {
  observe railway::RailwayElement::id = [696];
  observe railway::TrackElement::monitoredBy = [@o413];
  observe railway::TrackElement::connectsTo = [@o708];
  observe railway::Segment::length = [943];
  observe railway::Segment::semaphores = [];
}

object o708 : railway::Segment {
  observe railway::RailwayElement::id = [698];
  observe railway::TrackElement::monitoredBy = [@o414];
  observe railway::TrackElement::connectsTo = [@o709];
  observe railway::Segment::length = [354];
  observe railway::Segment::semaphores = [];
}

object o709 : railway::Segment {
  observe railway::RailwayElement::id = [699];
  observe railway::TrackElement::monitoredBy = [@o414];
  observe railway::TrackElement::connectsTo = [@o710];
  observe railway::Segment::length = [455];
  observe railway::Segment::semaphores = [];
}

object o710 : railway::Segment {
  observe railway::RailwayElement::id = [700];
  observe railway::TrackElement::monitoredBy = [@o414];
  observe railway::TrackElement::connectsTo = [@o711];
  observe railway::Segment::length = [272];
  observe railway::Segment::semaphores = [];
}

object o711 : railway::Segment {
  observe railway::RailwayElement::id = [701];
  observe railway::TrackElement::monitoredBy = [@o414];
  observe railway::TrackElement::connectsTo = [@o712];
  observe railway::Segment::length = [655];
  observe railway::Segment::semaphores = [];
}

object o712 : railway::Segment {
  observe railway::RailwayElement::id = [702];
  observe railway::TrackElement::monitoredBy = [@o414];
  observe railway::TrackElement::connectsTo = [@o713];
  observe railway::Segment::length = [411];
  observe railway::Segment::semaphores = [];
}

object o713 : railway::Segment {
  observe railway::RailwayElement::id = [704];
  observe railway::TrackElement::monitoredBy = [@o415];
  observe railway::TrackElement::connectsTo = [@o714];
  observe railway::Segment::length = [867];
  observe railway::Segment::semaphores = [];
}

object o714 : railway::Segment {
  observe railway::RailwayElement::id = [705];
  observe railway::TrackElement::monitoredBy = [@o415];
  observe railway::TrackElement::connectsTo = [@o715];
  observe railway::Segment::length = [212];
  observe railway::Segment::semaphores = [];
}

object o715 : railway::Segment {
  observe railway::RailwayElement::id = [706];
  observe railway::TrackElement::monitoredBy = [@o415];
  observe railway::TrackElement::connectsTo = [@o716];
  observe railway::Segment::length = [546];
  observe railway::Segment::semaphores = [];
}

object o716 : railway::Segment {
  observe railway::RailwayElement::id = [707];
  observe railway::TrackElement::monitoredBy = [@o415];
  observe railway::TrackElement::connectsTo = [@o717];
  observe railway::Segment::length = [570];
  observe railway::Segment::semaphores = [];
}

object o717 : railway::Segment {
  observe railway::RailwayElement::id = [708];
  observe railway::TrackElement::monitoredBy = [@o415];
  observe railway::TrackElement::connectsTo = [@o718];
  observe railway::Segment::length = [399];
  observe railway::Segment::semaphores = [];
}

object o718 : railway::Segment {
  observe railway::RailwayElement::id = [710];
  observe railway::TrackElement::monitoredBy = [@o416];
  observe railway::TrackElement::connectsTo = [@o719];
  observe railway::Segment::length = [645];
  observe railway::Segment::semaphores = [];
}

object o719 : railway::Segment {
  observe railway::RailwayElement::id = [711];
  observe railway::TrackElement::monitoredBy = [@o416];
  observe railway::TrackElement::connectsTo = [@o720];
  observe railway::Segment::length = [250];
  observe railway::Segment::semaphores = [];
}

object o720 : railway::Segment {
  observe railway::RailwayElement::id = [712];
  observe railway::TrackElement::monitoredBy = [@o416];
  observe railway::TrackElement::connectsTo = [@o721];
  observe railway::Segment::length = [344];
  observe railway::Segment::semaphores = [];
}

object o721 : railway::Segment {
  observe railway::RailwayElement::id = [713];
  observe railway::TrackElement::monitoredBy = [@o416];
  observe railway::TrackElement::connectsTo = [@o722];
  observe railway::Segment::length = [553];
  observe railway::Segment::semaphores = [];
}

object o722 : railway::Segment {
  observe railway::RailwayElement::id = [714];
  observe railway::TrackElement::monitoredBy = [@o416];
  observe railway::TrackElement::connectsTo = [@o723];
  observe railway::Segment::length = [17];
  observe railway::Segment::semaphores = [];
}

object o723 : railway::Segment {
  observe railway::RailwayElement::id = [716];
  observe railway::TrackElement::monitoredBy = [@o417];
  observe railway::TrackElement::connectsTo = [@o724];
  observe railway::Segment::length = [643];
  observe railway::Segment::semaphores = [];
}

object o724 : railway::Segment {
  observe railway::RailwayElement::id = [717];
  observe railway::TrackElement::monitoredBy = [@o417];
  observe railway::TrackElement::connectsTo = [@o725];
  observe railway::Segment::length = [572];
  observe railway::Segment::semaphores = [];
}

object o725 : railway::Segment {
  observe railway::RailwayElement::id = [718];
  observe railway::TrackElement::monitoredBy = [@o417];
  observe railway::TrackElement::connectsTo = [@o726];
  observe railway::Segment::length = [458];
  observe railway::Segment::semaphores = [];
}

object o726 : railway::Segment {
  observe railway::RailwayElement::id = [719];
  observe railway::TrackElement::monitoredBy = [@o417];
  observe railway::TrackElement::connectsTo = [@o727];
  observe railway::Segment::length = [261];
  observe railway::Segment::semaphores = [];
}

object o727 : railway::Segment {
  observe railway::RailwayElement::id = [720];
  observe railway::TrackElement::monitoredBy = [@o417];
  observe railway::TrackElement::connectsTo = [@o728];
  observe railway::Segment::length = [319];
  observe railway::Segment::semaphores = [];
}

object o728 : railway::Switch {
  observe railway::RailwayElement::id = [722];
  observe railway::TrackElement::monitoredBy = [@o418, @o419, @o420, @o421, @o422];
  observe railway::TrackElement::connectsTo = [@o729];
  observe railway::Switch::currentPosition = [];
  observe railway::Switch::positions = [@o23];
}

object o729 : railway::Segment {
  observe railway::RailwayElement::id = [724];
  observe railway::TrackElement::monitoredBy = [@o418];
  observe railway::TrackElement::connectsTo = [@o730];
  observe railway::Segment::length = [27];
  observe railway::Segment::semaphores = [];
}

object o730 : railway::Segment {
  observe railway::RailwayElement::id = [725];
  observe railway::TrackElement::monitoredBy = [@o418];
  observe railway::TrackElement::connectsTo = [@o731];
  observe railway::Segment::length = [795];
  observe railway::Segment::semaphores = [];
}

object o731 : railway::Segment {
  observe railway::RailwayElement::id = [726];
  observe railway::TrackElement::monitoredBy = [@o418];
  observe railway::TrackElement::connectsTo = [@o732];
  observe railway::Segment::length = [156];
  observe railway::Segment::semaphores = [];
}

object o732 : railway::Segment {
  observe railway::RailwayElement::id = [727];
  observe railway::TrackElement::monitoredBy = [@o418];
  observe railway::TrackElement::connectsTo = [@o733];
  observe railway::Segment::length = [479];
  observe railway::Segment::semaphores = [];
}

object o733 : railway::Segment {
  observe railway::RailwayElement::id = [728];
  observe railway::TrackElement::monitoredBy = [@o418];
  observe railway::TrackElement::connectsTo = [@o734];
  observe railway::Segment::length = [514];
  observe railway::Segment::semaphores = [];
}

object o734 : railway::Segment {
  observe railway::RailwayElement::id = [730];
  observe railway::TrackElement::monitoredBy = [@o419];
  observe railway::TrackElement::connectsTo = [@o735];
  observe railway::Segment::length = [748];
  observe railway::Segment::semaphores = [];
}

object o735 : railway::Segment {
  observe railway::RailwayElement::id = [731];
  observe railway::TrackElement::monitoredBy = [@o419];
  observe railway::TrackElement::connectsTo = [@o736];
  observe railway::Segment::length = [899];
  observe railway::Segment::semaphores = [];
}

object o736 : railway::Segment {
  observe railway::RailwayElement::id = [732];
  observe railway::TrackElement::monitoredBy = [@o419];
  observe railway::TrackElement::connectsTo = [@o737];
  observe railway::Segment::length = [15];
  observe railway::Segment::semaphores = [];
}

object o737 : railway::Segment {
  observe railway::RailwayElement::id = [733];
  observe railway::TrackElement::monitoredBy = [@o419];
  observe railway::TrackElement::connectsTo = [@o738];
  observe railway::Segment::length = [103];
  observe railway::Segment::semaphores = [];
}

object o738 : railway::Segment {
  observe railway::RailwayElement::id = [734];
  observe railway::TrackElement::monitoredBy = [@o419];
  observe railway::TrackElement::connectsTo = [@o739];
  observe railway::Segment::length = [623];
  observe railway::Segment::semaphores = [];
}

object o739 : railway::Segment {
  observe railway::RailwayElement::id = [736];
  observe railway::TrackElement::monitoredBy = [@o420];
  observe railway::TrackElement::connectsTo = [@o740];
  observe railway::Segment::length = [281];
  observe railway::Segment::semaphores = [];
}

object o740 : railway::Segment {
  observe railway::RailwayElement::id = [737];
  observe railway::TrackElement::monitoredBy = [@o420];
  observe railway::TrackElement::connectsTo = [@o741];
  observe railway::Segment::length = [141];
  observe railway::Segment::semaphores = [];
}

object o741 : railway::Segment {
  observe railway::RailwayElement::id = [738];
  observe railway::TrackElement::monitoredBy = [@o420];
  observe railway::TrackElement::connectsTo = [@o742];
  observe railway::Segment::length = [53];
  observe railway::Segment::semaphores = [];
}

object o742 : railway::Segment {
  observe railway::RailwayElement::id = [739];
  observe railway::TrackElement::monitoredBy = [@o420];
  observe railway::TrackElement::connectsTo = [@o743];
  observe railway::Segment::length = [915];
  observe railway::Segment::semaphores = [];
}

object o743 : railway::Segment {
  observe railway::RailwayElement::id = [740];
  observe railway::TrackElement::monitoredBy = [@o420];
  observe railway::TrackElement::connectsTo = [@o744];
  observe railway::Segment::length = [302];
  observe railway::Segment::semaphores = [];
}

object o744 : railway::Segment {
  observe railway::RailwayElement::id = [742];
  observe railway::TrackElement::monitoredBy = [@o421];
  observe railway::TrackElement::connectsTo = [@o745];
  observe railway::Segment::length = [145];
  observe railway::Segment::semaphores = [];
}

object o745 : railway::Segment {
  observe railway::RailwayElement::id = [743];
  observe railway::TrackElement::monitoredBy = [@o421];
  observe railway::TrackElement::connectsTo = [@o746];
  observe railway::Segment::length = [841];
  observe railway::Segment::semaphores = [];
}

object o746 : railway::Segment {
  observe railway::RailwayElement::id = [744];
  observe railway::TrackElement::monitoredBy = [@o421];
  observe railway::TrackElement::connectsTo = [@o747];
  observe railway::Segment::length = [410];
  observe railway::Segment::semaphores = [];
}

object o747 : railway::Segment {
  observe railway::RailwayElement::id = [745];
  observe railway::TrackElement::monitoredBy = [@o421];
  observe railway::TrackElement::connectsTo = [@o748];
  observe railway::Segment::length = [653];
  observe railway::Segment::semaphores = [];
}

object o748 : railway::Segment {
  observe railway::RailwayElement::id = [746];
  observe railway::TrackElement::monitoredBy = [@o421];
  observe railway::TrackElement::connectsTo = [@o749];
  observe railway::Segment::length = [123];
  observe railway::Segment::semaphores = [];
}

object o749 : railway::Segment {
  observe railway::RailwayElement::id = [748];
  observe railway::TrackElement::monitoredBy = [@o422];
  observe railway::TrackElement::connectsTo = [@o750];
  observe railway::Segment::length = [464];
  observe railway::Segment::semaphores = [];
}

object o750 : railway::Segment {
  observe railway::RailwayElement::id = [749];
  observe railway::TrackElement::monitoredBy = [@o422];
  observe railway::TrackElement::connectsTo = [@o751];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [];
}

object o751 : railway::Segment {
  observe railway::RailwayElement::id = [750];
  observe railway::TrackElement::monitoredBy = [@o422];
  observe railway::TrackElement::connectsTo = [@o752];
  observe railway::Segment::length = [236];
  observe railway::Segment::semaphores = [];
}

object o752 : railway::Segment {
  observe railway::RailwayElement::id = [751];
  observe railway::TrackElement::monitoredBy = [@o422];
  observe railway::TrackElement::connectsTo = [@o753];
  observe railway::Segment::length = [572];
  observe railway::Segment::semaphores = [];
}

object o753 : railway::Segment {
  observe railway::RailwayElement::id = [752];
  observe railway::TrackElement::monitoredBy = [@o422];
  observe railway::TrackElement::connectsTo = [@o32];
  observe railway::Segment::length = [647];
  observe railway::Segment::semaphores = [];
}
