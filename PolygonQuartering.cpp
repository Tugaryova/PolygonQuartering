#include <iostream>
#include <algorithm>
#include <vector>
#include <cmath>

const double cEpsilon = 0.0001;
const size_t cMaxSteps = 80;

struct Point
{
  Point() :
    m_x(0),
    m_y(0)
  {}

  Point(double coordX, double coordY) :
    m_x(coordX),
    m_y(coordY)
  {}

  bool operator==(Point point)
  {
    return std::abs(m_x - point.m_x) < cEpsilon && std::abs(m_y - point.m_y) < cEpsilon;
  }

  bool operator!=(Point point)
  {
    return !(*this == point);
  }

  double m_x;
  double m_y;
};

struct Line
{
  Line(double coefA, double coefB, double coefC) :
    m_a(coefA),
    m_b(coefB),
    m_c(coefC)
  {}

  Line(Point pointA, Point pointB) :
    m_a(pointA.m_y - pointB.m_y),
    m_b(pointB.m_x - pointA.m_x),
    m_c(pointA.m_x * pointB.m_y - pointB.m_x * pointA.m_y)
  {}

  explicit Line(double angle) :
    m_a(-sin(angle)),
    m_b(cos(angle)),
    m_c(0)
  {}

  double m_a;
  double m_b;
  double m_c;
};

double Area(Point pointA, Point pointB, Point pointC)
{
  double detA = pointA.m_x * (pointB.m_y - pointC.m_y);
  double detB = pointB.m_x * (pointC.m_y - pointA.m_y);
  double detC = pointC.m_x * (pointA.m_y - pointB.m_y);
  return std::abs((detA + detB + detC) / 2);
}

typedef std::vector<Point> Polygon;
typedef Polygon::const_iterator Iterator;

double Area(const Polygon& polygon)
{
  double sum = 0;
  size_t size = polygon.size();
  for (size_t it = 1; it < size - 1; ++it)
    sum += Area(polygon[0], polygon[it], polygon[it + 1]);
  return sum;
}

double Det(double aa, double bb, double cc, double dd)
{
  return aa * dd - bb * cc;
}

Point Intersection(Line lineL, Line lineM)
{  
  double denom = Det(lineL.m_a, lineL.m_b, lineM.m_a, lineM.m_b);
  double nomX = -Det(lineL.m_c, lineL.m_b, lineM.m_c, lineM.m_b);
  double nomY = -Det(lineL.m_a, lineL.m_c, lineM.m_a, lineM.m_c);
  return Point(nomX / denom, nomY / denom);
}

enum Sign
{
  negative = -1, 
  zero, 
  positive
};

Sign Substitute(Line line, Point point)
{
  double value = line.m_a * point.m_x + line.m_b * point.m_y + line.m_c;
  if (value >= cEpsilon)
    return positive;
  else if (value < -cEpsilon)
    return negative;
  else 
    return zero;
}

std::vector<Sign> SignVector(Line line, const Polygon& polygon, 
                           size_t& zerNumber, size_t& posNumber, size_t& negNumber)
{
  std::vector<Sign> signVector;
  size_t size = polygon.size();
  
  for (size_t it = 0; it < size; ++it)
  {
    Sign sign = Substitute(line, polygon[it]);
    if (sign == positive)
      ++posNumber;
    else if (sign == negative)
      ++negNumber;
    else
      ++zerNumber;
    signVector.push_back(Substitute(line, polygon[it]));
  } 
  return signVector;
}

Sign Substitute(Line line, const Polygon& polygon, double& areaL, double& areaR, 
                Polygon& halfL, Polygon& halfR)
{
  areaL = -1;
  areaR = -2;
  halfL.clear();
  halfR.clear();
  
  double areaTotal = Area(polygon);
  
  size_t size = polygon.size();
  size_t zerNumber = 0;
  size_t posNumber = 0;
  size_t negNumber = 0;
  
  std::vector<Sign> signVector = SignVector(line, polygon, zerNumber, posNumber, negNumber);
  if (posNumber == 0)
    return negative;
  if (negNumber == 0)
    return positive;

  Sign etalon = zero;
  int tmp = signVector[0] == zero ? -signVector[1] : -signVector[0];
  if (tmp == 1)
    etalon = positive;
  else
    etalon = negative;
  Sign nonEtalon = etalon == positive ? negative : positive;
  
  size_t it = 0;
  size_t mark = 0;
  while (signVector[it] != etalon)
    ++it;
  if (signVector[it - 1] == zero)
  {
    halfL.push_back(polygon[it - 1]);
    mark = it - 2;
  }
  else
  {
    halfL.push_back(Intersection(line, Line(polygon[it], polygon[it - 1])));
    mark = it - 1;
  }
  while (it < size && signVector[it] == etalon)
  {
    halfL.push_back(polygon[it]);
    ++it;
  }
  size_t prev = it == size ? 0 : it - 1;
  size_t remain = it % size;
  if (signVector[remain] == zero)
    halfL.push_back(polygon[remain]);
  else
    halfL.push_back(Intersection(line, Line(polygon[remain], polygon[it - 1])));

  halfR.push_back(halfL.back());
  for (size_t jt = it; jt < size; ++jt)
  {
    halfR.push_back(polygon[jt]);
  }
  for (size_t jt = 0; jt <= mark; ++jt)
  {
    halfR.push_back(polygon[jt]);
  }
  halfR.push_back(halfL.front());

  areaL = Area(halfL);
  areaR = Area(halfR);
  double areaDiff = areaL - areaR;

  if (areaDiff > cEpsilon)
    return etalon;
  else if (areaDiff < -cEpsilon)
    return nonEtalon;
  else
    return zero;
}

void SetTermBorders(Line line, double& min, double& max)
{
  double coef = 16000 / sqrt(line.m_a * line.m_a + line.m_b * line.m_b);
  double coordX = line.m_a * coef;
  double coordY = line.m_b * coef;
 
  min = - line.m_a * coordX - line.m_b * coordY;
  max = -min;
  if (min > max)
    std::swap(min, max);
}

void MoveLine(Line& line, const Polygon& polygon, double& areaL, double& areaR,
              Polygon& halfL, Polygon& halfR)
{
  double min = 0;
  double max = 0;
  SetTermBorders(line, min, max);

  line.m_c = min;
  Sign signMin = Substitute(line, polygon, areaL, areaR, halfL, halfR);
  
  double current = 0;
  line.m_c = current;
  Sign signCurrent = Substitute(line, polygon, areaL, areaR, halfL, halfR);

  size_t steps = 0;
  double error = std::abs(areaL - areaR);

  while (steps < cMaxSteps && error > cEpsilon)
  {
    if (signCurrent == zero)
      return;
    else if (signCurrent == signMin)
      min = current;
    else
      max = current;
    current = (min + max) / 2;
    line.m_c = current;
    signCurrent = Substitute(line, polygon, areaL, areaR, halfL, halfR);
    ++steps;
  }
}

double TermDifference(Line& line, const Polygon& polygon, Point& center)
{
  double areaL = 0;
  double areaR = 0;
  Polygon halfL;
  Polygon halfR;
  MoveLine(line, polygon, areaL, areaR, halfL, halfR);

  double areaU = 0;
  double areaD = 0;
  Polygon halfU;
  Polygon halfD;
  Line ortoL(line.m_b, -line.m_a, 0);
  Line ortoR(line.m_b, -line.m_a, 0);
  MoveLine(ortoL, halfL, areaU, areaD, halfU, halfD);
  MoveLine(ortoR, halfR, areaU, areaD, halfU, halfD);
  
  Point interLeft = Intersection(line, ortoL);
  Point interRight = Intersection(line, ortoR);
  
  center.m_x = (interLeft.m_x + interRight.m_x) / 2;
  center.m_y = (interLeft.m_y + interRight.m_y) / 2;
  
  return ortoL.m_c - ortoR.m_c;
}

void FindSection(const Polygon& polygon, double& angle, Point& center)
{
  double min = 0;
  double max = 3.1415926535;
  Line lineMin(min);
  double diffMin = TermDifference(lineMin, polygon, center);
  
  double current = (min + max) / 2;
  Line line(current);
  double diffCurrent = TermDifference(line, polygon, center);
  
  size_t steps = 0;
  while (steps < cMaxSteps && std::abs(diffCurrent) > cEpsilon)
  {
    if (diffCurrent * diffMin > 0)
      min = current;
    else
      max = current;
    current = (min + max) / 2;
    line = Line(current);
    diffCurrent = TermDifference(line, polygon, center);    
    ++steps;
  }

  angle = current * 180 / 3.1415926535;
}

int main()
{
  size_t size = 0;
  std::cin >> size;
  Polygon polygon;
  for (size_t it = 0; it < size; ++it)
  {
    double coordX = 0;
    double coordY = 0;
    std::cin >> coordX >> coordY;
    polygon.push_back(Point(coordX, coordY));
  }

  Point center;
  double angle;
  FindSection(polygon, angle, center);
  std::cout << center.m_x << " " << center.m_y << std::endl;
  std::cout << angle << std::endl;
  return 0;
}
